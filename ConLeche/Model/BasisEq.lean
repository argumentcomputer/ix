module

public import ConLeche.Model.BasisQuot
import ConLeche.Semantics.BasisRules
/- `ConLeche.Kernel.PropWhen` seals its representation on purpose (the
`Std.HashMap` pattern, task #194): the datum's module is `public` but not
`@[expose]`d, so a `cases`-then-`rfl` proof cannot see the reduct.
`import all` restores that view HERE only. -/
import all ConLeche.Kernel.PropWhen

public section

/-!
# The `Eq` block, P tier (task #161, ENDGAME H)

The one block the layer does not carry: there is no `BConst` for `Eq`,
so nothing here goes through `BConst.typeAV`/`BitAgree`/`bval_mem_type`
— every type reading's grading and membership is discharged against
the block's **own** towers (`Interp/EqTowerP.lean`), which is exactly
why the ENDGAME E seal built them first.

Two structural consequences:

* the `Eq` cons is the tier's one `eq_law`-bespoke cons
  (`eqLaw_cons_fresh`'s side condition is `eqName ≠ c₀.name`), and it
  is discharged by `eqLaw_of_tower` through
  `declStep_preserves_of_basis_cons_eqrow`;
* `Eq.rec`'s stored rule returns its **minor premise**, so its fired
  equality is an identity between two collapsed towers rather than a
  value law — and the only real content is that the major premise's
  membership forces `a = b` and the proof to be `pt`.

The three constants' bits are forced, not chosen (ENDGAME E §1):
`Eq`'s three binders are `.never`, `Eq.refl`'s two are
`.ifAllZero []`, and `Eq.rec`'s six are `.ifAllZero [u_1]`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm eqValT eqReflValT eqRecValT)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule uN u1N vN)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

section Eq

open ConLeche (eqA eqReflA eqRecA eqName eqReflName)

variable {m : EnvModel V env} {A : (Name → Nat) → AnnotTerm}

/-! ## The two spines the block's types are built from -/

/-- `@Eq.{u} α a b`, read through the tower. -/
def eqSpine (ψ : Name → Nat) (i j k : Nat) : AnnotTerm :=
  .app (.app (.app (eqValAV ψ) (.bvar i)) (.bvar j)) (.bvar k)

/-- `@Eq.refl.{u} α a`, read through the tower. -/
def eqReflSpine (ψ : Name → Nat) (i j : Nat) : AnnotTerm :=
  .app (.app (eqReflValAV ψ) (.bvar i)) (.bvar j)

theorem eqSpine_interp {ψ : Name → Nat} {i j k : Nat} {ρ : Nat → V}
    {Aset a b : V} (hi : ρ i = Aset) (hj : ρ j = a) (hk : ρ k = b)
    (hA : Aset ∈ˢ (univ (ψ uN) : V)) (ha : a ∈ˢ Aset) (hb : b ∈ˢ Aset) :
    interp V ρ (eqSpine ψ i j k) = eqv a b ∧
      WellDenotedV V ρ (eqSpine ψ i j k) ∧
      interp V ρ (eqSpine ψ i j k) ∈ˢ (univZero : V) := by
  have hAi : interp V ρ (AnnotTerm.bvar i) = Aset := by
    rw [interp_bvar, hi]
  have haj : interp V ρ (AnnotTerm.bvar j) = a := by
    rw [interp_bvar, hj]
  have hbk : interp V ρ (AnnotTerm.bvar k) = b := by
    rw [interp_bvar, hk]
  obtain ⟨hok, hz⟩ := eqValAV_app₃_okP ψ ρ (Aa := .bvar i) (la := .bvar j)
    (ra := .bvar k) ⟨trivial, trivial⟩ ⟨trivial, trivial⟩
    ⟨trivial, trivial⟩ (by rw [hAi]; exact hA)
    (by rw [hAi, haj]; exact ha) (by rw [hAi, hbk]; exact hb)
  refine ⟨?_, hok, hz⟩
  rw [eqSpine, interp_app, interp_app, interp_app, hAi, haj, hbk,
    eqValAV_app₃ ψ ρ Aset a b hA ha hb]

theorem eqReflSpine_data {ψ : Name → Nat} {i j : Nat} {ρ : Nat → V}
    {Aset a : V} (hi : ρ i = Aset) (hj : ρ j = a)
    (hA : Aset ∈ˢ (univ (ψ uN) : V)) (ha : a ∈ˢ Aset) :
    interp V ρ (eqReflSpine ψ i j) = (pt : V) ∧
      WellDenotedV V ρ (eqReflSpine ψ i j) := by
  have hpt : interp V ρ (eqReflValAV ψ) = (pt : V) :=
    eqReflValAV_interp ψ ρ
  have hAi : interp V ρ (AnnotTerm.bvar i) = Aset := by
    rw [interp_bvar, hi]
  have haj : interp V ρ (AnnotTerm.bvar j) = a := by
    rw [interp_bvar, hj]
  have h1 := WellDenotedV_app_pt (S := (univ (ψ uN) : V))
    (a := AnnotTerm.bvar i) (eqReflValAV_wellDenotedV ψ ρ) hpt
    ⟨trivial, trivial⟩ (by rw [hAi]; exact hA)
  have h2 := WellDenotedV_app_pt (S := Aset) (a := AnnotTerm.bvar j)
    h1.1 h1.2 ⟨trivial, trivial⟩ (by rw [haj]; exact ha)
  exact ⟨h2.2, h2.1⟩

/-! ## `Eq` and `Eq.refl` -/

/-- `Eq`'s type reading: three graph-regime binders. -/
@[expose] def eqTy (ψ : Name → Nat) : AnnotTerm :=
  .pi 0 1 (.sort (ψ uN)) (.pi 0 1 (.bvar 0) (.pi 0 1 (.bvar 1) (.sort 0)))

/-- `Eq.refl`'s type reading: two squash-regime binders over the
spine. -/
def eqReflTy (ψ : Name → Nat) : AnnotTerm :=
  .pi 0 0 (.sort (ψ uN)) (.pi 0 0 (.bvar 0) (eqSpine ψ 1 0 0))

/-- **`Eq`'s type reading.** -/
theorem denoteMeta_eqA_type
    {acval : Name → (Name → Nat) → AnnotTerm} (ψ : Name → Nat) :
    denoteMeta acval ⟨eqA :: env.consts⟩ ψ 0 eqA.toConstantVal.type
      = some (eqTy ψ) := by
  simp [eqA, ConstantInfo.toConstantVal, denoteMeta_forallE, denoteMeta_sort,
    denoteMeta_fvar, Expr.instantiate1, eqTy, pwBit_never, Level.eval, uN]

theorem eqTy_wellDenotedV (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenotedV V ρ (eqTy ψ) :=
  ⟨⟨trivial, fun _ _ => ⟨trivial, fun _ _ => ⟨trivial,
      fun _ _ => trivial⟩⟩⟩,
    ⟨trivial, fun _ _ => ⟨trivial, fun _ _ => ⟨trivial,
        fun _ _ => trivial, fun h => absurd h Nat.one_ne_zero⟩,
      fun h => absurd h Nat.one_ne_zero⟩,
    fun h => absurd h Nat.one_ne_zero⟩⟩

theorem eqTy_interp (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (eqTy ψ)
      = piR 1 (univ (ψ uN) : V)
          (fun a => piR 1 a (fun _ => piR 1 a (fun _ => univZero))) := by
  rw [eqTy, interp_pi, interp_sort]
  refine piR_congr fun a _ => ?_
  rw [interp_pi]
  simp only [interp_bvar, cons]
  refine piR_congr fun x _ => ?_
  rw [interp_pi]
  simp only [interp_bvar, interp_sort, cons]
  exact piR_congr fun _ _ => univ_zero

/-- **`Eq.refl`'s type reading.**  Stated at *any* extension whose
cons is not `Eq`, because `Eq.rec`'s row reads it as its fired
constructor's telescope. -/
theorem denoteMeta_eqReflTy {c₀ : ConstantInfo} (ψ : Name → Nat)
    (hne : ¬ c₀.name = eqName)
    (hE : env.find? eqName = some eqA)
    (hEv : ∀ ψ : Name → Nat, m.acval eqName ψ = eqValAV ψ) :
    denoteMeta (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ 0
        eqReflA.toConstantVal.type
      = some (eqReflTy ψ) := by
  have hEc : ∀ d : Nat,
      denoteMeta (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d
        (.const eqName [.param uN]) = some (eqValAV ψ) := by
    intro d
    rw [denoteMeta_eqLeaf (m := m) (A := A) ψ (Level.param uN) hne hE d,
      show ([Level.param uN] : List Level)
        = List.map Level.param [uN] from rfl,
      Level.substFn_param_self ψ [uN], hEv]
  rw [show eqReflA.toConstantVal.type
      = Expr.forallE (.sort (.param uN))
          (Expr.forallE (.bvar 0)
            (.app (.app (.app (.const eqName [.param uN]) (.bvar 1))
              (.bvar 0)) (.bvar 0))
            { pw := .ifAllZero [] })
          { pw := .ifAllZero [] } from rfl]
  simp [denoteMeta_forallE, denoteMeta_sort, denoteMeta_app, denoteMeta_fvar,
    Expr.instantiate1, eqReflTy, eqSpine, pwBit_ifAllZero_nil, hEc,
    Level.eval]

theorem eqReflTy_data (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenotedV V ρ (eqReflTy ψ) ∧
      interp V ρ (eqReflTy ψ)
        = piR 0 (univ (ψ uN) : V) (fun a => piR 0 a (fun x => eqv x x)) := by
  have hstep : ∀ Aset x : V, Aset ∈ˢ (univ (ψ uN) : V) → x ∈ˢ Aset →
      interp V (cons x (cons Aset ρ)) (eqSpine ψ 1 0 0) = eqv x x ∧
      WellDenotedV V (cons x (cons Aset ρ)) (eqSpine ψ 1 0 0) ∧
      interp V (cons x (cons Aset ρ)) (eqSpine ψ 1 0 0)
        ∈ˢ (univZero : V) := by
    intro Aset x hA hx
    exact eqSpine_interp (ρ := cons x (cons Aset ρ))
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hA hx hx
  constructor
  · rw [eqReflTy]
    refine (WellDenotedV_pi_zero (Aa := .sort (ψ uN)) ⟨trivial, trivial⟩
      ?_ ?_).1
    all_goals (
      intro Aset hAset
      rw [interp_sort] at hAset
      have hlev := WellDenotedV_pi_zero (Aa := AnnotTerm.bvar 0)
        (ρ := cons Aset ρ) ⟨trivial, trivial⟩
        (fun x hx => (hstep Aset x hAset
          (by simpa [interp_bvar, cons] using hx)).2.1)
        (fun x hx => (hstep Aset x hAset
          (by simpa [interp_bvar, cons] using hx)).2.2))
    case _ => exact hlev.1
    case _ => exact hlev.2
  · rw [eqReflTy, interp_pi, interp_sort]
    refine piR_congr fun Aset hAset => ?_
    rw [interp_pi]
    simp only [interp_bvar, cons]
    exact piR_congr fun x hx => (hstep Aset x hAset hx).1

/-! ### The two installs -/

/-- **`Eq`, installed at the P tier** — the tier's one `eq_law`
bespoke cons. -/
theorem extendEq (mp : EnvModelM V μ env)
    (hfresh : env.find? eqName = none)
    (hwf : EnvWF ⟨eqA :: env.consts⟩) :
    ∃ mp' : EnvModelM V μ ⟨eqA :: env.consts⟩,
      mp'.base2.acval
        = acvalWith mp.base2.acval eqA.name eqValAV := by
  refine declStep_preserves_of_basis_cons_eqrow mp (A := eqValAV) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h) (by decide)
    (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf
      (fun ψ => by rw [eqValAV_erase ψ]; exact eqValT_closed ψ)
      rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT eqA.name ψ
          = none from rfl] at hp
        exact nomatch hp)
      (fun _ h => nomatch h) (fun _ _ _ _ h => nomatch h))
    (fun ψ k => AnnotTerm.liftN_eq_self _
      (Term.bvarsBelow.mono (Nat.zero_le k)
        (by rw [eqValAV_erase]; exact eqValT_closed ψ)) 1)
    (fun ψ₁ ψ₂ hp => eqValAV_congr
      (hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)))
    (fun ψ ρ => eqValAV_wellDenoted ψ ρ) (fun ψ ρ => eqValAV_validV ψ ρ)
    (fun ψ => ⟨_, denoteMeta_eqA_type ψ⟩) ?_ ?_ ?_
  · intro ψ ta h ρ
    rw [denoteMeta_eqA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact eqTy_wellDenotedV ψ ρ
  · intro ψ ta h ρ
    rw [denoteMeta_eqA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [eqTy_interp]
    exact eqValAV_mem ψ ρ
  · intro m₂ hac
    refine eqLaw_of_tower m₂ fun ψ => ?_
    rw [hac, show eqName = eqA.name from rfl, acvalWith_self]

/-- **`Eq.refl`, installed at the P tier.** -/
theorem extendEqRefl (mp : EnvModelM V μ env)
    (hE : env.find? eqName = some eqA)
    (hEv : ∀ ψ : Name → Nat, mp.base2.acval eqName ψ = eqValAV ψ)
    (hfresh : env.find? eqReflA.name = none)
    (hwf : EnvWF ⟨eqReflA :: env.consts⟩) :
    ∃ mp' : EnvModelM V μ ⟨eqReflA :: env.consts⟩,
      mp'.base2.acval
        = acvalWith mp.base2.acval eqReflA.name eqReflValAV := by
  have hty := fun ψ =>
    denoteMeta_eqReflTy (m := mp.base2) (A := eqReflValAV) (c₀ := eqReflA)
      ψ (by decide) hE hEv
  refine declStep_preserves_of_basis_cons mp (A := eqReflValAV) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf
      (fun ψ => by rw [eqReflValAV_erase ψ]; exact eqReflValT_closed ψ)
      rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT eqReflA.name ψ
          = none from rfl] at hp
        exact nomatch hp)
      (fun _ h => nomatch h) (fun _ _ _ _ h => nomatch h))
    (fun ψ k => AnnotTerm.liftN_eq_self _
      (Term.bvarsBelow.mono (Nat.zero_le k)
        (by rw [eqReflValAV_erase]; exact eqReflValT_closed ψ)) 1)
    (fun ψ₁ ψ₂ hp => eqReflValAV_congr
      (hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)))
    (fun ψ ρ => eqReflValAV_wellDenoted ψ ρ)
    (fun ψ ρ => eqReflValAV_validV ψ ρ)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact (eqReflTy_data ψ ρ).1
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [(eqReflTy_data ψ ρ).2]
    exact eqReflValAV_mem ψ ρ

/-! ## `Eq.rec`

Its six binders are pinned `.ifAllZero [u_1]` — the *motive* level's
zero test, not the type's — so the whole constant lives at one bit `b`
with `b = 0 ↔ ψ u_1 = 0`.  Its rule returns the minor premise, so the
only real content anywhere in the block is that the major premise's
membership forces `a = b` and the proof to be `pt`: an inhabitant of
`eqv a b` gives `a = b` by `mem_eqv`, and `eqv` is a truth value, so
the inhabitant is the canonical proof by `mem_univ_zero`.

`eqRecValAV`'s membership and grading are the two items the ENDGAME E
seal recorded as owed; both are below. -/

/-- `Eq.rec`'s motive binder domain reading. -/
def eqRecMotiveTy (ψ : Name → Nat) : AnnotTerm :=
  .pi 0 1 (.bvar 1) (.pi 0 1 (eqSpine ψ 2 1 0) (.sort (ψ u1N)))

/-- `Eq.rec`'s minor binder domain reading. -/
def eqRecMinorTy (ψ : Name → Nat) : AnnotTerm :=
  .app (.app (.bvar 0) (.bvar 1)) (eqReflSpine ψ 2 1)

/-- `Eq.rec`'s type reading. -/
def eqRecTy (b : Nat) (ψ : Name → Nat) : AnnotTerm :=
  .pi 0 b (.sort (ψ uN))
    (.pi 0 b (.bvar 0)
      (.pi 0 b (eqRecMotiveTy ψ)
        (.pi 0 b (eqRecMinorTy ψ)
          (.pi 0 b (.bvar 3)
            (.pi 0 b (eqSpine ψ 4 3 0)
              (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))))))

/-- `Eq.rec`'s rule's RHS reading: the same four domains, over the
minor premise. -/
def eqRecRa (b : Nat) (ψ : Name → Nat) : AnnotTerm :=
  .lam b (.sort (ψ uN))
    (.lam b (.bvar 0)
      (.lam b (eqRecMotiveTy ψ)
        (.lam b (eqRecMinorTy ψ) (.bvar 0))))

/-- The motive space: `∀ b, a = b → Sort u₁`. -/
noncomputable def eqRecMotiveSpace (V : Type w) [SetTheory V]
    (u1 : Nat) (Aset a : V) : V :=
  piR 1 Aset fun b => piR 1 (eqv a b) fun _ => (univ u1 : V)

theorem eqRecMotiveTy_data {ψ : Name → Nat} {Aset a : V}
    (ρ : Nat → V) (hA : Aset ∈ˢ (univ (ψ uN) : V)) (ha : a ∈ˢ Aset) :
    interp V (cons a (cons Aset ρ)) (eqRecMotiveTy ψ)
        = eqRecMotiveSpace V (ψ u1N) Aset a ∧
      WellDenotedV V (cons a (cons Aset ρ)) (eqRecMotiveTy ψ) := by
  have hsp : ∀ b : V, b ∈ˢ Aset →
      interp V (cons b (cons a (cons Aset ρ))) (eqSpine ψ 2 1 0)
          = eqv a b ∧
        WellDenotedV V (cons b (cons a (cons Aset ρ))) (eqSpine ψ 2 1 0) ∧
        interp V (cons b (cons a (cons Aset ρ))) (eqSpine ψ 2 1 0)
          ∈ˢ (univZero : V) := fun b hb =>
    eqSpine_interp (ρ := cons b (cons a (cons Aset ρ)))
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hA ha hb
  have hdom : interp V (cons a (cons Aset ρ)) (AnnotTerm.bvar 1)
      = Aset := by simp [interp_bvar, cons]
  refine ⟨?_, ?_⟩
  · rw [eqRecMotiveTy, interp_pi, eqRecMotiveSpace, hdom]
    refine piR_congr fun b hb => ?_
    rw [interp_pi, (hsp b hb).1]
    exact piR_congr fun _ _ => interp_sort V _ _
  · refine ⟨⟨trivial, fun b hb => ?_⟩,
      ⟨trivial, fun b hb => ?_, fun h => absurd h Nat.one_ne_zero⟩⟩
    · rw [hdom] at hb
      exact ⟨(hsp b hb).2.1.1, fun _ _ => trivial⟩
    · rw [hdom] at hb
      exact ⟨(hsp b hb).2.1.2, fun _ _ => trivial,
        fun h => absurd h Nat.one_ne_zero⟩

theorem eqRecMinorTy_data {ψ : Name → Nat} {Aset a M : V}
    (ρ : Nat → V) (hA : Aset ∈ˢ (univ (ψ uN) : V)) (ha : a ∈ˢ Aset)
    (hM : M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a) :
    interp V (cons M (cons a (cons Aset ρ))) (eqRecMinorTy ψ)
        = app (app M a) pt ∧
      WellDenotedV V (cons M (cons a (cons Aset ρ))) (eqRecMinorTy ψ) ∧
      app (app M a) pt ∈ˢ (univ (ψ u1N) : V) := by
  obtain ⟨hrint, hrok⟩ := eqReflSpine_data (ψ := ψ) (i := 2) (j := 1)
    (ρ := cons M (cons a (cons Aset ρ)))
    (by simp [cons]) (by simp [cons]) hA ha
  have hM0 : M ∈ˢ piR 1 Aset (fun b => piR 1 (eqv a b)
      fun _ => (univ (ψ u1N) : V)) := hM
  have hMa : app M a ∈ˢ piR 1 (eqv a a) fun _ => (univ (ψ u1N) : V) :=
    app_mem_piR_pos Nat.one_ne_zero hM0 ha
  have hMap : app (app M a) pt ∈ˢ (univ (ψ u1N) : V) :=
    app_mem_piR_pos Nat.one_ne_zero hMa (pt_mem_eqv_self a)
  have hMb : interp V (cons M (cons a (cons Aset ρ)))
      (AnnotTerm.bvar 0) = M := by simp [interp_bvar, cons]
  have hab : interp V (cons M (cons a (cons Aset ρ)))
      (AnnotTerm.bvar 1) = a := by simp [interp_bvar, cons]
  refine ⟨?_, ⟨?_, ?_⟩, hMap⟩
  · rw [eqRecMinorTy, interp_app, interp_app, hrint, hMb, hab]
  · rw [eqRecMinorTy, WellDenoted_app]
    refine ⟨?_, hrok.1, 1, eqv a a, fun _ => (univ (ψ u1N) : V), ?_,
      by rw [hrint]; exact pt_mem_eqv_self a,
      fun h => absurd h Nat.one_ne_zero⟩
    · rw [WellDenoted_app]
      exact ⟨trivial, trivial, 1, Aset,
        fun b => piR 1 (eqv a b) fun _ => (univ (ψ u1N) : V),
        by rw [hMb]; exact hM0, by rw [hab]; exact ha,
        fun h => absurd h Nat.one_ne_zero⟩
    · rw [interp_app, hMb, hab]; exact hMa
  · exact ⟨⟨trivial, trivial⟩, hrok.2⟩

/-- **The major premise collapses the block**: an inhabitant of
`eqv a b` identifies `a` with `b` and is itself the canonical proof.
This is `Eq.rec`'s entire iota content, and it is why the layer does
not carry the constant at all (`eqRec_derivable`). -/
theorem eqRec_major_collapse {a b h : V} (hh : h ∈ˢ eqv a b) :
    a = b ∧ h = pt :=
  ⟨mem_eqv hh, mem_univ_zero (univ_zero (V := V) ▸ eqv_mem_univZero a b) hh⟩

/-! ### The tower, bit-cleaned

`eqRecValAV` carries the *type's* result sort `ψ u_1 + 1` at the
motive domain's inner binder where the reading carries `pwBit … .never
= 1`.  The two agree on zero-ness and on nothing else is read, so they
are `BitAgree` — which is the whole distance between the tower the
ENDGAME E seal built and the tower this block's walk wants. -/

/-- The tower with the reading's own numerals. -/
def eqRecRaTower (b : Nat) (ψ : Name → Nat) : AnnotTerm :=
  .lam b (.sort (ψ uN))
    (.lam b (.bvar 0)
      (.lam b (eqRecMotiveTy ψ)
        (.lam b (eqRecMinorTy ψ)
          (.lam b (.bvar 3)
            (.lam b (eqSpine ψ 4 3 0) (.bvar 2))))))

theorem bitAgree_eqRecValAV (ψ : Name → Nat) :
    AnnotTerm.BitAgree (eqRecRaTower (pwBit ψ (.ifAllZero [u1N])) ψ)
      (eqRecValAV ψ) :=
  .lam Iff.rfl (.sort _)
    (.lam Iff.rfl (.bvar 0)
      (.lam Iff.rfl
        (.pi Iff.rfl (.bvar 1)
          (.pi (Iff.intro (fun h => absurd h Nat.one_ne_zero)
              (fun h => absurd h (Nat.succ_ne_zero _)))
            (AnnotTerm.BitAgree.refl _) (.sort _)))
        (.lam Iff.rfl (AnnotTerm.BitAgree.refl _)
          (.lam Iff.rfl (.bvar 3)
            (.lam Iff.rfl (AnnotTerm.BitAgree.refl _) (.bvar 2))))))

/-- **`Eq.rec`'s tower is graded and inhabits its type's reading** —
the two items the ENDGAME E seal recorded as owed, taken in one walk
(`WellDenotedV_lam_mem` six times).  The only content is at the bottom:
the major premise collapses `b` onto `a` and itself onto `pt`, and the
minor premise is already there. -/
theorem eqRecRaTower_data {b : Nat} (ψ : Name → Nat)
    (hz : b = 0 ↔ ψ u1N = 0) (ρ : Nat → V) :
    WellDenotedV V ρ (eqRecRaTower b ψ) ∧
      interp V ρ (eqRecRaTower b ψ)
        ∈ˢ interp V ρ (eqRecTy b ψ) := by
  have hzero : ∀ x : V, x ∈ˢ (univ (ψ u1N) : V) → b = 0 →
      x ∈ˢ (univZero : V) := fun x hx hb => by
    rw [← univ_zero, ← hz.mp hb]; exact hx
  -- level 6: the body, at a fixed major premise
  have h6 : ∀ Aset a M mn bb : V, Aset ∈ˢ (univ (ψ uN) : V) →
      a ∈ˢ Aset → M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a →
      mn ∈ˢ app (app M a) pt → bb ∈ˢ Aset →
      WellDenotedV V (cons bb (cons mn (cons M (cons a (cons Aset ρ)))))
          (.lam b (eqSpine ψ 4 3 0) (.bvar 2)) ∧
        interp V (cons bb (cons mn (cons M (cons a (cons Aset ρ)))))
            (.lam b (eqSpine ψ 4 3 0) (.bvar 2))
          ∈ˢ piR b (eqv a bb) (fun h => app (app M bb) h) := by
    intro Aset a M mn bb hA ha hM hmn hbb
    obtain ⟨hsint, hsok, -⟩ := eqSpine_interp
      (ρ := cons bb (cons mn (cons M (cons a (cons Aset ρ)))))
      (i := 4) (j := 3) (k := 0)
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hA ha hbb
    have hM0 : M ∈ˢ piR 1 Aset (fun x => piR 1 (eqv a x)
        fun _ => (univ (ψ u1N) : V)) := hM
    have hMb : app M bb ∈ˢ piR 1 (eqv a bb)
        fun _ => (univ (ψ u1N) : V) :=
      app_mem_piR_pos Nat.one_ne_zero hM0 hbb
    have key : ∀ h : V, h ∈ˢ eqv a bb →
        app (app M bb) h = app (app M a) pt ∧
          app (app M bb) h ∈ˢ (univ (ψ u1N) : V) := by
      intro h hh
      obtain ⟨hab, hpt⟩ := eqRec_major_collapse (V := V) hh
      refine ⟨by rw [hab, hpt], ?_⟩
      exact app_mem_piR_pos Nat.one_ne_zero hMb hh
    have hstep := WellDenotedV_lam_mem (V := V) (b := b)
      (Aa := eqSpine ψ 4 3 0) (bd := .bvar 2)
      (F := fun h => app (app M bb) h) hsok
      (fun h hh => by
        rw [hsint] at hh
        refine ⟨⟨trivial, trivial⟩, ?_⟩
        rw [show interp V (cons h (cons bb (cons mn (cons M
            (cons a (cons Aset ρ)))))) (AnnotTerm.bvar 2) = mn
          from by simp [interp_bvar, cons], (key h hh).1]
        exact hmn)
      (fun hb h hh => by
        rw [hsint] at hh
        exact hzero _ (key h hh).2 hb)
    rw [hsint] at hstep
    exact hstep
  -- level 5
  have h5 : ∀ Aset a M mn : V, Aset ∈ˢ (univ (ψ uN) : V) →
      a ∈ˢ Aset → M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a →
      mn ∈ˢ app (app M a) pt →
      WellDenotedV V (cons mn (cons M (cons a (cons Aset ρ))))
          (.lam b (.bvar 3) (.lam b (eqSpine ψ 4 3 0) (.bvar 2))) ∧
        interp V (cons mn (cons M (cons a (cons Aset ρ))))
            (.lam b (.bvar 3) (.lam b (eqSpine ψ 4 3 0) (.bvar 2)))
          ∈ˢ piR b Aset
            (fun bb => piR b (eqv a bb) fun h => app (app M bb) h) := by
    intro Aset a M mn hA ha hM hmn
    have hdom : interp V (cons mn (cons M (cons a (cons Aset ρ))))
        (AnnotTerm.bvar 3) = Aset := by simp [interp_bvar, cons]
    have hstep := WellDenotedV_lam_mem (V := V) (b := b)
      (Aa := AnnotTerm.bvar 3)
      (bd := .lam b (eqSpine ψ 4 3 0) (.bvar 2))
      (F := fun bb => piR b (eqv a bb) fun h => app (app M bb) h)
      ⟨trivial, trivial⟩
      (fun bb hbb => h6 Aset a M mn bb hA ha hM hmn
        (by rwa [hdom] at hbb))
      (fun hb _ _ => by rw [hb]; exact piR_zero_mem_univZero)
    rw [hdom] at hstep
    exact hstep
  -- level 4
  have h4 : ∀ Aset a M : V, Aset ∈ˢ (univ (ψ uN) : V) → a ∈ˢ Aset →
      M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a →
      WellDenotedV V (cons M (cons a (cons Aset ρ)))
          (.lam b (eqRecMinorTy ψ)
            (.lam b (.bvar 3)
              (.lam b (eqSpine ψ 4 3 0) (.bvar 2)))) ∧
        interp V (cons M (cons a (cons Aset ρ)))
            (.lam b (eqRecMinorTy ψ)
              (.lam b (.bvar 3)
                (.lam b (eqSpine ψ 4 3 0) (.bvar 2))))
          ∈ˢ piR b (app (app M a) pt) (fun _ => piR b Aset
            (fun bb => piR b (eqv a bb) fun h => app (app M bb) h)) := by
    intro Aset a M hA ha hM
    obtain ⟨hmint, hmok, -⟩ := eqRecMinorTy_data ρ hA ha hM
    have hstep := WellDenotedV_lam_mem (V := V) (b := b)
      (Aa := eqRecMinorTy ψ)
      (F := fun _ => piR b Aset
        (fun bb => piR b (eqv a bb) fun h => app (app M bb) h))
      hmok
      (fun mn hmn => h5 Aset a M mn hA ha hM (by rwa [hmint] at hmn))
      (fun hb _ _ => by rw [hb]; exact piR_zero_mem_univZero)
    rw [hmint] at hstep
    exact hstep
  -- level 3
  have h3 : ∀ Aset a : V, Aset ∈ˢ (univ (ψ uN) : V) → a ∈ˢ Aset →
      WellDenotedV V (cons a (cons Aset ρ))
          (.lam b (eqRecMotiveTy ψ)
            (.lam b (eqRecMinorTy ψ)
              (.lam b (.bvar 3)
                (.lam b (eqSpine ψ 4 3 0) (.bvar 2))))) ∧
        interp V (cons a (cons Aset ρ))
            (.lam b (eqRecMotiveTy ψ)
              (.lam b (eqRecMinorTy ψ)
                (.lam b (.bvar 3)
                  (.lam b (eqSpine ψ 4 3 0) (.bvar 2)))))
          ∈ˢ piR b (eqRecMotiveSpace V (ψ u1N) Aset a)
            (fun M => piR b (app (app M a) pt) (fun _ => piR b Aset
              (fun bb => piR b (eqv a bb)
                fun h => app (app M bb) h))) := by
    intro Aset a hA ha
    obtain ⟨hmint, hmok⟩ := eqRecMotiveTy_data ρ hA ha
    have hstep := WellDenotedV_lam_mem (V := V) (b := b)
      (Aa := eqRecMotiveTy ψ)
      (F := fun M => piR b (app (app M a) pt) (fun _ => piR b Aset
        (fun bb => piR b (eqv a bb) fun h => app (app M bb) h)))
      hmok
      (fun M hM => h4 Aset a M hA ha (by rwa [hmint] at hM))
      (fun hb _ _ => by rw [hb]; exact piR_zero_mem_univZero)
    rw [hmint] at hstep
    exact hstep
  -- level 2
  have h2 : ∀ Aset : V, Aset ∈ˢ (univ (ψ uN) : V) →
      WellDenotedV V (cons Aset ρ)
          (.lam b (.bvar 0)
            (.lam b (eqRecMotiveTy ψ)
              (.lam b (eqRecMinorTy ψ)
                (.lam b (.bvar 3)
                  (.lam b (eqSpine ψ 4 3 0) (.bvar 2)))))) ∧
        interp V (cons Aset ρ)
            (.lam b (.bvar 0)
              (.lam b (eqRecMotiveTy ψ)
                (.lam b (eqRecMinorTy ψ)
                  (.lam b (.bvar 3)
                    (.lam b (eqSpine ψ 4 3 0) (.bvar 2))))))
          ∈ˢ piR b Aset (fun a =>
            piR b (eqRecMotiveSpace V (ψ u1N) Aset a)
              (fun M => piR b (app (app M a) pt) (fun _ => piR b Aset
                (fun bb => piR b (eqv a bb)
                  fun h => app (app M bb) h)))) := by
    intro Aset hA
    have hdom : interp V (cons Aset ρ) (AnnotTerm.bvar 0) = Aset := by
      simp [interp_bvar, cons]
    have hstep := WellDenotedV_lam_mem (V := V) (b := b)
      (Aa := AnnotTerm.bvar 0)
      (F := fun a => piR b (eqRecMotiveSpace V (ψ u1N) Aset a)
        (fun M => piR b (app (app M a) pt) (fun _ => piR b Aset
          (fun bb => piR b (eqv a bb) fun h => app (app M bb) h))))
      ⟨trivial, trivial⟩
      (fun a ha => h3 Aset a hA (by rwa [hdom] at ha))
      (fun hb _ _ => by rw [hb]; exact piR_zero_mem_univZero)
    rw [hdom] at hstep
    exact hstep
  have hstep := WellDenotedV_lam_mem (V := V) (b := b)
    (Aa := .sort (ψ uN))
    (F := fun Aset => piR b Aset (fun a =>
      piR b (eqRecMotiveSpace V (ψ u1N) Aset a)
        (fun M => piR b (app (app M a) pt) (fun _ => piR b Aset
          (fun bb => piR b (eqv a bb) fun h => app (app M bb) h)))))
    ⟨trivial, trivial⟩
    (fun Aset hA => h2 Aset (by rwa [interp_sort] at hA))
    (fun hb _ _ => by rw [hb]; exact piR_zero_mem_univZero)
  refine ⟨hstep.1, ?_⟩
  rw [interp_sort] at hstep
  refine (?_ : interp V ρ (eqRecTy b ψ)
    = piR b (univ (ψ uN) : V) (fun Aset => piR b Aset (fun a =>
      piR b (eqRecMotiveSpace V (ψ u1N) Aset a)
        (fun M => piR b (app (app M a) pt) (fun _ => piR b Aset
          (fun bb => piR b (eqv a bb)
            fun h => app (app M bb) h)))))) ▸ hstep.2
  -- the type reading's own six products, in the same order
  rw [eqRecTy, interp_pi, interp_sort]
  refine piR_congr fun Aset hAset => ?_
  rw [interp_pi]
  simp only [interp_bvar, cons]
  refine piR_congr fun a ha => ?_
  rw [interp_pi, (eqRecMotiveTy_data ρ hAset ha).1]
  refine piR_congr fun M hM => ?_
  rw [interp_pi, (eqRecMinorTy_data ρ hAset ha hM).1]
  refine piR_congr fun mn _ => ?_
  rw [interp_pi]
  simp only [interp_bvar, cons]
  refine piR_congr fun bb hbb => ?_
  rw [interp_pi,
    (eqSpine_interp (ρ := cons bb (cons mn (cons M (cons a
        (cons Aset ρ))))) (i := 4) (j := 3) (k := 0)
      (by simp [cons]) (by simp [cons]) (by simp [cons])
      hAset ha hbb).1]
  refine piR_congr fun h _ => ?_
  simp [interp_app, interp_bvar, cons]

/-! ### The two readings -/

/-- **`Eq.rec`'s type reading.** -/
theorem denoteMeta_eqRecA_type (ψ : Name → Nat)
    (hE : env.find? eqName = some eqA)
    (hR : env.find? eqReflName = some eqReflA)
    (hEv : ∀ ψ : Name → Nat, m.acval eqName ψ = eqValAV ψ)
    (hRv : ∀ ψ : Name → Nat, m.acval eqReflName ψ = eqReflValAV ψ) :
    denoteMeta (acvalWith m.acval eqRecA.name A)
        ⟨eqRecA :: env.consts⟩ ψ 0 eqRecA.toConstantVal.type
      = some (eqRecTy (pwBit ψ (.ifAllZero [u1N])) ψ) := by
  have hEc : ∀ d : Nat,
      denoteMeta (acvalWith m.acval eqRecA.name A)
        ⟨eqRecA :: env.consts⟩ ψ d (.const eqName [.param uN])
        = some (eqValAV ψ) := by
    intro d
    rw [denoteMeta_eqLeaf (m := m) (A := A) ψ (Level.param uN)
        (by decide) hE d,
      show ([Level.param uN] : List Level)
        = List.map Level.param [uN] from rfl,
      Level.substFn_param_self ψ [uN], hEv]
  have hRc : ∀ d : Nat,
      denoteMeta (acvalWith m.acval eqRecA.name A)
        ⟨eqRecA :: env.consts⟩ ψ d (.const eqReflName [.param uN])
        = some (eqReflValAV ψ) := by
    intro d
    have hf' : (⟨eqRecA :: env.consts⟩ : Env).find? eqReflName
        = some eqReflA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hR
    rw [denoteMeta_const hf' (by rfl), acvalWith_ne (by decide),
      show Level.substFn ψ eqReflA.toConstantVal.levelParams
        [Level.param uN] = Level.substFn ψ [uN]
          (List.map Level.param [uN]) from rfl,
      Level.substFn_param_self ψ [uN], hRv]
  rw [show eqRecA.toConstantVal.type
      = Expr.forallE (.sort (.param uN))
          (Expr.forallE (.bvar 0)
            (Expr.forallE
              (Expr.forallE (.bvar 1)
                (Expr.forallE
                  (.app (.app (.app (.const eqName [.param uN])
                    (.bvar 2)) (.bvar 1)) (.bvar 0))
                  (.sort (.param u1N))
                  { pw := .never })
                { pw := .never })
              (Expr.forallE
                (.app (.app (.bvar 0) (.bvar 1))
                  (.app (.app (.const eqReflName [.param uN])
                    (.bvar 2)) (.bvar 1)))
                (Expr.forallE (.bvar 3)
                  (Expr.forallE
                    (.app (.app (.app (.const eqName [.param uN])
                      (.bvar 4)) (.bvar 3)) (.bvar 0))
                    (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))
                    { pw := .ifAllZero [u1N] })
                  { pw := .ifAllZero [u1N] })
                { pw := .ifAllZero [u1N] })
              { pw := .ifAllZero [u1N] })
            { pw := .ifAllZero [u1N] })
          { pw := .ifAllZero [u1N] } from rfl]
  simp [denoteMeta_forallE, denoteMeta_sort, denoteMeta_app, denoteMeta_fvar,
    Expr.instantiate1, eqRecTy, eqRecMotiveTy, eqRecMinorTy,
    eqSpine, eqReflSpine, pwBit_never, hEc, hRc, Level.eval]

/-- **`Eq.rec`'s rule's RHS reading.** -/
theorem denoteMeta_eqRec_rhs (ψ : Name → Nat)
    (hE : env.find? eqName = some eqA)
    (hR : env.find? eqReflName = some eqReflA)
    (hEv : ∀ ψ : Name → Nat, m.acval eqName ψ = eqValAV ψ)
    (hRv : ∀ ψ : Name → Nat, m.acval eqReflName ψ = eqReflValAV ψ) :
    denoteMeta (acvalWith m.acval eqRecA.name A)
        ⟨eqRecA :: env.consts⟩ ψ 0 eqRecRule.rhs
      = some (eqRecRa (pwBit ψ (.ifAllZero [u1N])) ψ) := by
  have hEc : ∀ d : Nat,
      denoteMeta (acvalWith m.acval eqRecA.name A)
        ⟨eqRecA :: env.consts⟩ ψ d (.const eqName [.param uN])
        = some (eqValAV ψ) := by
    intro d
    rw [denoteMeta_eqLeaf (m := m) (A := A) ψ (Level.param uN)
        (by decide) hE d,
      show ([Level.param uN] : List Level)
        = List.map Level.param [uN] from rfl,
      Level.substFn_param_self ψ [uN], hEv]
  have hRc : ∀ d : Nat,
      denoteMeta (acvalWith m.acval eqRecA.name A)
        ⟨eqRecA :: env.consts⟩ ψ d (.const eqReflName [.param uN])
        = some (eqReflValAV ψ) := by
    intro d
    have hf' : (⟨eqRecA :: env.consts⟩ : Env).find? eqReflName
        = some eqReflA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hR
    rw [denoteMeta_const hf' (by rfl), acvalWith_ne (by decide),
      show Level.substFn ψ eqReflA.toConstantVal.levelParams
        [Level.param uN] = Level.substFn ψ [uN]
          (List.map Level.param [uN]) from rfl,
      Level.substFn_param_self ψ [uN], hRv]
  simp only [eqRecRule]
  simp [denoteMeta_lam, denoteMeta_forallE, denoteMeta_sort, denoteMeta_app,
    denoteMeta_fvar, Expr.instantiate1, eqRecRa, eqRecMotiveTy,
    eqRecMinorTy, eqSpine, eqReflSpine, pwBit_never, hEc, hRc,
    Level.eval]

/-! ### The RHS tower and the two firing sides -/

/-- The product the RHS tower inhabits. -/
noncomputable def eqRecRaSpace (V : Type w) [SetTheory V]
    (b u u1 : Nat) : V :=
  piR b (univ u : V) fun Aset => piR b Aset fun a =>
    piR b (eqRecMotiveSpace V u1 Aset a) fun M =>
      piR b (app (app M a) pt) fun _ => app (app M a) pt

theorem eqRecRa_data {b : Nat} (ψ : Name → Nat)
    (hz : b = 0 ↔ ψ u1N = 0) (ρ : Nat → V) :
    WellDenotedV V ρ (eqRecRa b ψ) ∧
      interp V ρ (eqRecRa b ψ)
        ∈ˢ eqRecRaSpace V b (ψ uN) (ψ u1N) := by
  have hzero : ∀ x : V, x ∈ˢ (univ (ψ u1N) : V) → b = 0 →
      x ∈ˢ (univZero : V) := fun x hx hb => by
    rw [← univ_zero, ← hz.mp hb]; exact hx
  have h4 : ∀ Aset a M : V, Aset ∈ˢ (univ (ψ uN) : V) → a ∈ˢ Aset →
      M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a →
      WellDenotedV V (cons M (cons a (cons Aset ρ)))
          (.lam b (eqRecMinorTy ψ) (.bvar 0)) ∧
        interp V (cons M (cons a (cons Aset ρ)))
            (.lam b (eqRecMinorTy ψ) (.bvar 0))
          ∈ˢ piR b (app (app M a) pt) (fun _ => app (app M a) pt) := by
    intro Aset a M hA ha hM
    obtain ⟨hmint, hmok, hmuniv⟩ := eqRecMinorTy_data ρ hA ha hM
    have hstep := WellDenotedV_lam_mem (V := V) (b := b)
      (Aa := eqRecMinorTy ψ) (bd := .bvar 0)
      (F := fun _ => app (app M a) pt) hmok
      (fun mn hmn => by
        rw [hmint] at hmn
        exact ⟨⟨trivial, trivial⟩, by
          rw [show interp V (cons mn (cons M (cons a (cons Aset ρ))))
            (AnnotTerm.bvar 0) = mn from by simp [interp_bvar, cons]]
          exact hmn⟩)
      (fun hb _ _ => hzero _ hmuniv hb)
    rw [hmint] at hstep
    exact hstep
  have h3 : ∀ Aset a : V, Aset ∈ˢ (univ (ψ uN) : V) → a ∈ˢ Aset →
      WellDenotedV V (cons a (cons Aset ρ))
          (.lam b (eqRecMotiveTy ψ)
            (.lam b (eqRecMinorTy ψ) (.bvar 0))) ∧
        interp V (cons a (cons Aset ρ))
            (.lam b (eqRecMotiveTy ψ)
              (.lam b (eqRecMinorTy ψ) (.bvar 0)))
          ∈ˢ piR b (eqRecMotiveSpace V (ψ u1N) Aset a)
            (fun M => piR b (app (app M a) pt)
              (fun _ => app (app M a) pt)) := by
    intro Aset a hA ha
    obtain ⟨hmint, hmok⟩ := eqRecMotiveTy_data ρ hA ha
    have hstep := WellDenotedV_lam_mem (V := V) (b := b)
      (Aa := eqRecMotiveTy ψ)
      (F := fun M => piR b (app (app M a) pt)
        (fun _ => app (app M a) pt)) hmok
      (fun M hM => h4 Aset a M hA ha (by rwa [hmint] at hM))
      (fun hb _ _ => by rw [hb]; exact piR_zero_mem_univZero)
    rw [hmint] at hstep
    exact hstep
  have h2 : ∀ Aset : V, Aset ∈ˢ (univ (ψ uN) : V) →
      WellDenotedV V (cons Aset ρ)
          (.lam b (.bvar 0) (.lam b (eqRecMotiveTy ψ)
            (.lam b (eqRecMinorTy ψ) (.bvar 0)))) ∧
        interp V (cons Aset ρ)
            (.lam b (.bvar 0) (.lam b (eqRecMotiveTy ψ)
              (.lam b (eqRecMinorTy ψ) (.bvar 0))))
          ∈ˢ piR b Aset (fun a =>
            piR b (eqRecMotiveSpace V (ψ u1N) Aset a)
              (fun M => piR b (app (app M a) pt)
                (fun _ => app (app M a) pt))) := by
    intro Aset hA
    have hdom : interp V (cons Aset ρ) (AnnotTerm.bvar 0) = Aset := by
      simp [interp_bvar, cons]
    have hstep := WellDenotedV_lam_mem (V := V) (b := b)
      (Aa := AnnotTerm.bvar 0)
      (F := fun a => piR b (eqRecMotiveSpace V (ψ u1N) Aset a)
        (fun M => piR b (app (app M a) pt)
          (fun _ => app (app M a) pt)))
      ⟨trivial, trivial⟩
      (fun a ha => h3 Aset a hA (by rwa [hdom] at ha))
      (fun hb _ _ => by rw [hb]; exact piR_zero_mem_univZero)
    rw [hdom] at hstep
    exact hstep
  have hstep := WellDenotedV_lam_mem (V := V) (b := b)
    (Aa := .sort (ψ uN))
    (F := fun Aset => piR b Aset (fun a =>
      piR b (eqRecMotiveSpace V (ψ u1N) Aset a)
        (fun M => piR b (app (app M a) pt)
          (fun _ => app (app M a) pt))))
    ⟨trivial, trivial⟩
    (fun Aset hA => h2 Aset (by rwa [interp_sort] at hA))
    (fun hb _ _ => by rw [hb]; exact piR_zero_mem_univZero)
  rw [interp_sort] at hstep
  exact ⟨hstep.1, hstep.2⟩

/-- **`Eq.rec`'s recursor tower fires to the minor premise** — at
`b ≠ 0` by six `app_lamR_pos`, at `b = 0` because the motive's fibre
is then a truth value and the minor premise *is* the canonical
proof. -/
theorem eqRecRaTower_app₆ {b : Nat} (ψ : Name → Nat)
    (hz : b = 0 ↔ ψ u1N = 0) (ρ : Nat → V) {Aset a M mn bb h : V}
    (hA : Aset ∈ˢ (univ (ψ uN) : V)) (ha : a ∈ˢ Aset)
    (hM : M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a)
    (hmn : mn ∈ˢ app (app M a) pt) (hbb : bb ∈ˢ Aset)
    (hh : h ∈ˢ eqv a bb) :
    app (app (app (app (app (app
        (interp V ρ (eqRecRaTower b ψ)) Aset) a) M) mn) bb) h = mn := by
  obtain ⟨hmint, -, hmuniv⟩ := eqRecMinorTy_data ρ hA ha hM
  by_cases hb : b = 0
  · rw [eqRecRaTower, interp_lam, hb, lamR_zero, app_pt, app_pt,
      app_pt, app_pt, app_pt, app_pt]
    have h0 : app (app M a) pt ∈ˢ (univ 0 : V) := by
      rw [← hz.mp hb]; exact hmuniv
    exact (mem_univ_zero h0 hmn).symm
  · obtain ⟨hmoint, -⟩ := eqRecMotiveTy_data ρ hA ha
    obtain ⟨hsint, -, -⟩ := eqSpine_interp
      (ρ := cons bb (cons mn (cons M (cons a (cons Aset ρ)))))
      (i := 4) (j := 3) (k := 0)
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hA ha hbb
    rw [eqRecRaTower, interp_lam, interp_sort, app_lamR_pos hb hA,
      interp_lam,
      show interp V (cons Aset ρ) (AnnotTerm.bvar 0) = Aset
        from by simp [interp_bvar, cons],
      app_lamR_pos hb ha,
      interp_lam, hmoint, app_lamR_pos hb hM,
      interp_lam, hmint, app_lamR_pos hb hmn,
      interp_lam,
      show interp V (cons mn (cons M (cons a (cons Aset ρ))))
        (AnnotTerm.bvar 3) = Aset from by simp [interp_bvar, cons],
      app_lamR_pos hb hbb,
      interp_lam, hsint, app_lamR_pos hb hh]
    simp [interp_bvar, cons]

/-- …and the RHS tower's four-fold application is the same value. -/
theorem eqRecRa_app₄ {b : Nat} (ψ : Name → Nat)
    (hz : b = 0 ↔ ψ u1N = 0) (ρ : Nat → V) {Aset a M mn : V}
    (hA : Aset ∈ˢ (univ (ψ uN) : V)) (ha : a ∈ˢ Aset)
    (hM : M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a)
    (hmn : mn ∈ˢ app (app M a) pt) :
    app (app (app (app (interp V ρ (eqRecRa b ψ)) Aset) a) M) mn
      = mn := by
  obtain ⟨hmint, -, hmuniv⟩ := eqRecMinorTy_data ρ hA ha hM
  by_cases hb : b = 0
  · rw [eqRecRa, interp_lam, hb, lamR_zero, app_pt, app_pt, app_pt,
      app_pt]
    have h0 : app (app M a) pt ∈ˢ (univ 0 : V) := by
      rw [← hz.mp hb]; exact hmuniv
    exact (mem_univ_zero h0 hmn).symm
  · obtain ⟨hmoint, -⟩ := eqRecMotiveTy_data ρ hA ha
    rw [eqRecRa, interp_lam, interp_sort, app_lamR_pos hb hA,
      interp_lam,
      show interp V (cons Aset ρ) (AnnotTerm.bvar 0) = Aset
        from by simp [interp_bvar, cons],
      app_lamR_pos hb ha,
      interp_lam, hmoint, app_lamR_pos hb hM,
      interp_lam, hmint, app_lamR_pos hb hmn]
    simp [interp_bvar, cons]

/-! ### The row -/

theorem eqRecValAV_congr {ψ₁ ψ₂ : Name → Nat} (hu : ψ₁ uN = ψ₂ uN)
    (hu1 : ψ₁ u1N = ψ₂ u1N) : eqRecValAV ψ₁ = eqRecValAV ψ₂ := by
  have hb : pwBit ψ₁ (ConLeche.PropWhen.ifAllZero [u1N])
      = pwBit ψ₂ (ConLeche.PropWhen.ifAllZero [u1N]) := by
    unfold pwBit
    simp [hu1]
  rw [eqRecValAV, eqRecValAV, hb, hu, hu1, eqValAV_congr hu,
    eqReflValAV_congr hu]

set_option maxHeartbeats 1000000 in
/-- **`Eq.rec`'s `RecRuleLaw` row.**  The rule is `.plain`, so both
`.nested` conjuncts are `nomatch`; the fired equality is the minor
premise on both sides (`eqRecRaTower_app₆` against `eqRecRa_app₄`),
and the transport is four `WellDenotedV_app_of` steps. -/
theorem eqRecLaw {m : EnvModel V env}
    (m₂ : EnvModel V ⟨eqRecA :: env.consts⟩)
    (hE : env.find? eqName = some eqA)
    (hR : env.find? eqReflName = some eqReflA)
    (hEv : ∀ ψ : Name → Nat, m.acval eqName ψ = eqValAV ψ)
    (hRv : ∀ ψ : Name → Nat, m.acval eqReflName ψ = eqReflValAV ψ)
    (hac : m₂.acval = acvalWith m.acval eqRecA.name eqRecValAV)
    (φ : Name → Nat) :
    RecRuleLaw m₂ φ eqRecA.name eqRecA.toConstantVal 5 4
      eqRecRule := by
  refine ⟨by decide, fun us hus => ?_⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Name → Nat,
      ψ = Level.substFn φ eqRecA.toConstantVal.levelParams us :=
    ⟨_, rfl⟩
  have hz : pwBit ψ (ConLeche.PropWhen.ifAllZero [u1N]) = 0 ↔ ψ u1N = 0 :=
    pwBit_ifAllZero_single ψ u1N
  have hRa : denoteMeta m₂.acval ⟨eqRecA :: env.consts⟩ φ 0
      (eqRecRule.rhs.instantiateLevelParams
        eqRecA.toConstantVal.levelParams us)
      = some (eqRecRa (pwBit ψ (.ifAllZero [u1N])) ψ) := by
    rw [denoteMeta_instLevels (acvalParamsAt_of_core m₂) φ, hac, hψ,
      denoteMeta_eqRec_rhs (m := m) _ hE hR hEv hRv]
  refine ⟨_, hRa, fun ρ => (eqRecRa_data ψ hz ρ).1, ?_, ?_⟩
  · intro _ _ h
    exact nomatch h
  intro cvj cnP cnF hfj usj ρ xs ys TVa TVja restR restC hxs hys husj
    hlev _ hnested hpin hTVa hTVja hfitR hfitC
  have hR' : (⟨eqRecA :: env.consts⟩ : Env).find? eqReflName
      = some eqReflA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hR
  rw [show RecRule.ctor eqRecRule = eqReflName from rfl, hR'] at hfj
  obtain ⟨rfl, rfl, rfl⟩ :
      cvj = eqReflA.toConstantVal ∧ cnP = 2 ∧ cnF = 0 := by
    injection Option.some.inj hfj with a1 a2 a3
    exact ⟨a1.symm, a2.symm, a3.symm⟩
  obtain ⟨x1, x2, x3, x4, x5, rfl⟩ :
      ∃ p q r s t, xs = [p, q, r, s, t] := by
    match xs, hxs with
    | [p, q, r, s, t], _ => exact ⟨p, q, r, s, t, rfl⟩
  obtain ⟨y1, y2, rfl⟩ : ∃ p q, ys = [p, q] := by
    match ys, hys with
    | [p, q], _ => exact ⟨p, q, rfl⟩
  have hulev : Level.substFn φ eqReflA.toConstantVal.levelParams usj uN
      = ψ uN := by
    rw [congrFun hlev uN, hψ]
    show Level.eval φ (Level.subst eqRecA.toConstantVal.levelParams
      us (.param uN)) = _
    rw [Level.subst, Level.eval_subst_go]
  have hTyRead : denoteMeta m₂.acval ⟨eqRecA :: env.consts⟩ φ 0
      (eqRecA.toConstantVal.type.instantiateLevelParams
        eqRecA.toConstantVal.levelParams us)
      = some (eqRecTy (pwBit ψ (.ifAllZero [u1N])) ψ) := by
    rw [denoteMeta_instLevels (acvalParamsAt_of_core m₂) φ, hac, hψ,
      denoteMeta_eqRecA_type (m := m) _ hE hR hEv hRv]
  obtain rfl : TVa = _ :=
    (Option.some.inj (hTyRead.symm.trans hTVa)).symm
  have hCtorRead : denoteMeta m₂.acval ⟨eqRecA :: env.consts⟩ φ 0
      (eqReflA.toConstantVal.type.instantiateLevelParams
        eqReflA.toConstantVal.levelParams usj)
      = some (eqReflTy
          (Level.substFn φ eqReflA.toConstantVal.levelParams usj)) := by
    rw [denoteMeta_instLevels (acvalParamsAt_of_core m₂) φ, hac,
      denoteMeta_eqReflTy (m := m) _ (by decide) hE hEv]
  obtain rfl : TVja = _ :=
    (Option.some.inj (hCtorRead.symm.trans hTVja)).symm
  rw [eqRecTy] at hfitR
  cases hfitR with | cons f1 hfitR =>
  cases hfitR with | cons f2 hfitR =>
  cases hfitR with | cons f3 hfitR =>
  cases hfitR with | cons f4 hfitR =>
  cases hfitR with | cons f5 hfitR =>
  cases hfitR with | cons f6 _ =>
  rw [interp_sort] at f1
  rw [interp_inst0] at f2
  simp only [interp_bvar, cons] at f2
  rw [interp_inst0, interp_inst_cons1,
    (eqRecMotiveTy_data ρ f1 f2).1] at f3
  rw [interp_inst0, interp_inst_cons1, interp_inst_cons2,
    (eqRecMinorTy_data ρ f1 f2 f3).1] at f4
  rw [interp_inst0, interp_inst_cons1, interp_inst_cons2,
    interp_inst_cons3] at f5
  simp only [interp_bvar, cons] at f5
  rw [interp_inst0, interp_inst_cons1, interp_inst_cons2,
    interp_inst_cons3, interp_inst_cons4,
    (eqSpine_interp (ρ := cons (interp V ρ x5) (cons (interp V ρ x4)
        (cons (interp V ρ x3) (cons (interp V ρ x2)
          (cons (interp V ρ x1) ρ))))) (i := 4) (j := 3) (k := 0)
      (by simp [cons]) (by simp [cons]) (by simp [cons])
      f1 f2 f5).1] at f6
  rw [eqReflTy] at hfitC
  cases hfitC with | cons g1 hfitC =>
  cases hfitC with | cons g2 _ =>
  rw [hulev, interp_sort] at g1
  rw [interp_inst0] at g2
  simp only [interp_bvar, cons] at g2
  have hrecL : m₂.acval eqRecA.name
      (Level.substFn φ eqRecA.toConstantVal.levelParams us)
      = eqRecValAV ψ := by
    rw [hac, acvalWith_self, hψ]
  have hctorL : m₂.acval eqReflName
      (Level.substFn φ eqReflA.toConstantVal.levelParams usj)
      = eqReflValAV
        (Level.substFn φ eqReflA.toConstantVal.levelParams usj) := by
    rw [hac, acvalWith_ne (by decide), hRv]
  simp only [show RecRule.ctor eqRecRule = eqReflName from rfl,
    AnnotTerm.mkAppN_cons, AnnotTerm.mkAppN_nil, interp_app, hctorL,
    eqReflValAV_interp, app_pt] at f6
  refine ⟨?_, ?_⟩
  · -- the fired equality
    simp only [show RecRule.ctor eqRecRule = eqReflName from rfl,
      show eqRecRule.ctorParams = 2 from rfl,
      List.take, List.drop, List.cons_append, List.nil_append,
      List.append_nil, AnnotTerm.mkAppN_cons, AnnotTerm.mkAppN_nil, hrecL,
      interp_app, hctorL, eqReflValAV_interp, app_pt]
    rw [← AnnotTerm.BitAgree.interp_eq V (bitAgree_eqRecValAV ψ) ρ,
      eqRecRaTower_app₆ ψ hz ρ f1 f2 f3 f4 f5 f6,
      eqRecRa_app₄ ψ hz ρ f1 f2 f3 f4]
  · -- the transport
    intro hxsA _
    simp only [show eqRecRule.ctorParams = 2 from rfl,
      List.take, List.drop, List.append_nil,
      AnnotTerm.mkAppN_cons, AnnotTerm.mkAppN_nil]
    have hRm := (eqRecRa_data ψ hz ρ).2
    rw [eqRecRaSpace] at hRm
    have h1 := WellDenotedV_app_of ((eqRecRa_data ψ hz ρ).1)
      (hxsA x1 (by simp)) hRm f1
      (fun hb0 _ _ => by rw [hb0]; exact piR_zero_mem_univZero)
    have h2 := WellDenotedV_app_of h1.1 (hxsA x2 (by simp)) h1.2 f2
      (fun hb0 _ _ => by rw [hb0]; exact piR_zero_mem_univZero)
    have h3 := WellDenotedV_app_of h2.1 (hxsA x3 (by simp)) h2.2 f3
      (fun hb0 _ _ => by rw [hb0]; exact piR_zero_mem_univZero)
    exact (WellDenotedV_app_of h3.1 (hxsA x4 (by simp)) h3.2 f4
      (fun hb0 _ _ => by
        rw [← univ_zero, ← hz.mp hb0]
        exact (eqRecMinorTy_data ρ f1 f2 f3).2.2)).1

/-- **`Eq.rec`'s type reading is graded** — six `WellDenotedV_pi_bit`
steps; the innermost body is the motive applied to the major premise,
whose fibre is a truth value exactly when the bit is zero. -/
theorem eqRecTy_wellDenotedV {b : Nat} (ψ : Name → Nat)
    (hz : b = 0 ↔ ψ u1N = 0) (ρ : Nat → V) :
    WellDenotedV V ρ (eqRecTy b ψ) := by
  have h6 : ∀ Aset a M mn bb : V, Aset ∈ˢ (univ (ψ uN) : V) →
      a ∈ˢ Aset → M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a →
      bb ∈ˢ Aset →
      WellDenotedV V (cons bb (cons mn (cons M (cons a (cons Aset ρ)))))
        (.pi 0 b (eqSpine ψ 4 3 0)
          (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))) := by
    intro Aset a M mn bb hA ha hM hbb
    obtain ⟨hsint, hsok, -⟩ := eqSpine_interp
      (ρ := cons bb (cons mn (cons M (cons a (cons Aset ρ)))))
      (i := 4) (j := 3) (k := 0)
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hA ha hbb
    have hM0 : M ∈ˢ piR 1 Aset (fun x => piR 1 (eqv a x)
        fun _ => (univ (ψ u1N) : V)) := hM
    have hMb : app M bb ∈ˢ piR 1 (eqv a bb)
        fun _ => (univ (ψ u1N) : V) :=
      app_mem_piR_pos Nat.one_ne_zero hM0 hbb
    refine WellDenotedV_pi_bit hsok (fun h hh => ?_) (fun hb h hh => ?_)
    · rw [hsint] at hh
      refine ⟨?_, ⟨⟨trivial, trivial⟩, trivial⟩⟩
      rw [WellDenoted_app]
      refine ⟨?_, trivial, 1, eqv a bb, fun _ => (univ (ψ u1N) : V),
        ?_, ?_, fun hx => absurd hx Nat.one_ne_zero⟩
      · rw [WellDenoted_app]
        refine ⟨trivial, trivial, 1, Aset,
          fun x => piR 1 (eqv a x) fun _ => (univ (ψ u1N) : V), ?_, ?_,
          fun hx => absurd hx Nat.one_ne_zero⟩
        · rw [show interp V (cons h (cons bb (cons mn (cons M
              (cons a (cons Aset ρ)))))) (AnnotTerm.bvar 3) = M
            from by simp [interp_bvar, cons]]
          exact hM0
        · rw [show interp V (cons h (cons bb (cons mn (cons M
              (cons a (cons Aset ρ)))))) (AnnotTerm.bvar 1) = bb
            from by simp [interp_bvar, cons]]
          exact hbb
      · rw [interp_app,
          show interp V (cons h (cons bb (cons mn (cons M
              (cons a (cons Aset ρ)))))) (AnnotTerm.bvar 3) = M
            from by simp [interp_bvar, cons],
          show interp V (cons h (cons bb (cons mn (cons M
              (cons a (cons Aset ρ)))))) (AnnotTerm.bvar 1) = bb
            from by simp [interp_bvar, cons]]
        exact hMb
      · rw [show interp V (cons h (cons bb (cons mn (cons M
            (cons a (cons Aset ρ)))))) (AnnotTerm.bvar 0) = h
          from by simp [interp_bvar, cons]]
        exact hh
    · rw [hsint] at hh
      rw [interp_app, interp_app,
        show interp V (cons h (cons bb (cons mn (cons M
            (cons a (cons Aset ρ)))))) (AnnotTerm.bvar 3) = M
          from by simp [interp_bvar, cons],
        show interp V (cons h (cons bb (cons mn (cons M
            (cons a (cons Aset ρ)))))) (AnnotTerm.bvar 1) = bb
          from by simp [interp_bvar, cons],
        show interp V (cons h (cons bb (cons mn (cons M
            (cons a (cons Aset ρ)))))) (AnnotTerm.bvar 0) = h
          from by simp [interp_bvar, cons],
        ← univ_zero, ← hz.mp hb]
      exact app_mem_piR_pos Nat.one_ne_zero hMb hh
  have h5 : ∀ Aset a M mn : V, Aset ∈ˢ (univ (ψ uN) : V) →
      a ∈ˢ Aset → M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a →
      WellDenotedV V (cons mn (cons M (cons a (cons Aset ρ))))
        (.pi 0 b (.bvar 3) (.pi 0 b (eqSpine ψ 4 3 0)
          (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))) := by
    intro Aset a M mn hA ha hM
    have hdom : interp V (cons mn (cons M (cons a (cons Aset ρ))))
        (AnnotTerm.bvar 3) = Aset := by simp [interp_bvar, cons]
    refine WellDenotedV_pi_bit (Aa := .bvar 3) ⟨trivial, trivial⟩
      (fun bb hbb => h6 Aset a M mn bb hA ha hM (by rwa [hdom] at hbb))
      (fun hb _ _ => by rw [interp_pi, hb]; exact piR_zero_mem_univZero)
  have h4 : ∀ Aset a M : V, Aset ∈ˢ (univ (ψ uN) : V) → a ∈ˢ Aset →
      M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a →
      WellDenotedV V (cons M (cons a (cons Aset ρ)))
        (.pi 0 b (eqRecMinorTy ψ)
          (.pi 0 b (.bvar 3) (.pi 0 b (eqSpine ψ 4 3 0)
            (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))))) := by
    intro Aset a M hA ha hM
    obtain ⟨-, hmok, -⟩ := eqRecMinorTy_data ρ hA ha hM
    refine WellDenotedV_pi_bit hmok (fun mn _ => h5 Aset a M mn hA ha hM)
      (fun hb _ _ => by rw [interp_pi, hb]; exact piR_zero_mem_univZero)
  have h3 : ∀ Aset a : V, Aset ∈ˢ (univ (ψ uN) : V) → a ∈ˢ Aset →
      WellDenotedV V (cons a (cons Aset ρ))
        (.pi 0 b (eqRecMotiveTy ψ) (.pi 0 b (eqRecMinorTy ψ)
          (.pi 0 b (.bvar 3) (.pi 0 b (eqSpine ψ 4 3 0)
            (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))))) := by
    intro Aset a hA ha
    obtain ⟨hmint, hmok⟩ := eqRecMotiveTy_data ρ hA ha
    refine WellDenotedV_pi_bit hmok
      (fun M hM => h4 Aset a M hA ha (by rwa [hmint] at hM))
      (fun hb _ _ => by rw [interp_pi, hb]; exact piR_zero_mem_univZero)
  have h2 : ∀ Aset : V, Aset ∈ˢ (univ (ψ uN) : V) →
      WellDenotedV V (cons Aset ρ)
        (.pi 0 b (.bvar 0) (.pi 0 b (eqRecMotiveTy ψ)
          (.pi 0 b (eqRecMinorTy ψ)
            (.pi 0 b (.bvar 3) (.pi 0 b (eqSpine ψ 4 3 0)
              (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))))))) := by
    intro Aset hA
    have hdom : interp V (cons Aset ρ) (AnnotTerm.bvar 0) = Aset := by
      simp [interp_bvar, cons]
    refine WellDenotedV_pi_bit (Aa := .bvar 0) ⟨trivial, trivial⟩
      (fun a ha => h3 Aset a hA (by rwa [hdom] at ha))
      (fun hb _ _ => by rw [interp_pi, hb]; exact piR_zero_mem_univZero)
  rw [eqRecTy]
  refine WellDenotedV_pi_bit (Aa := .sort (ψ uN)) ⟨trivial, trivial⟩
    (fun Aset hA => h2 Aset (by rwa [interp_sort] at hA))
    (fun hb _ _ => by rw [interp_pi, hb]; exact piR_zero_mem_univZero)

/-- **`Eq.rec`, installed at the P tier.** -/
theorem extendEqRec (mp : EnvModelM V μ env)
    (hE : env.find? eqName = some eqA)
    (hR : env.find? eqReflName = some eqReflA)
    (hEv : ∀ ψ : Name → Nat, mp.base2.acval eqName ψ = eqValAV ψ)
    (hRv : ∀ ψ : Name → Nat,
      mp.base2.acval eqReflName ψ = eqReflValAV ψ)
    (hfresh : env.find? eqRecA.name = none)
    (hwf : EnvWF ⟨eqRecA :: env.consts⟩) :
    ∃ mp' : EnvModelM V μ ⟨eqRecA :: env.consts⟩,
      mp'.base2.acval
        = acvalWith mp.base2.acval eqRecA.name eqRecValAV := by
  have hty := fun ψ =>
    denoteMeta_eqRecA_type (m := mp.base2) (A := eqRecValAV) ψ hE hR hEv hRv
  have hz : ∀ ψ : Name → Nat,
      pwBit ψ (ConLeche.PropWhen.ifAllZero [u1N]) = 0 ↔ ψ u1N = 0 :=
    fun ψ => pwBit_ifAllZero_single ψ u1N
  refine declStep_preserves_of_basis_rec_cons mp (A := eqRecValAV) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf
      (fun ψ => by rw [eqRecValAV_erase ψ]; exact eqRecValT_closed ψ)
      rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT eqRecA.name ψ
          = none from rfl] at hp
        exact nomatch hp)
      (fun _ h => nomatch h)
      (fun _ _ _ _ heq r hr => by
        injection heq with _ _ _ h4
        rw [← h4] at hr
        rcases List.mem_cons.mp hr with rfl | hr'
        · exact ⟨⟨_, _, _, hR⟩, fun _ => recRuleKOf_of hR rfl hE rfl,
            fun hb => Bool.noConfusion hb⟩
        · exact nomatch hr'))
    (fun ψ k => AnnotTerm.liftN_eq_self _
      (Term.bvarsBelow.mono (Nat.zero_le k)
        (by rw [eqRecValAV_erase]; exact eqRecValT_closed ψ)) 1)
    (fun ψ₁ ψ₂ hp => eqRecValAV_congr
      (hp uN (by
        show uN ∈ [u1N, uN]
        exact List.mem_cons_of_mem _ List.mem_cons_self))
      (hp u1N (by show u1N ∈ [u1N, uN]; exact List.mem_cons_self)))
    (fun ψ ρ => ((bitAgree_wellDenotedV (bitAgree_eqRecValAV ψ) ρ).mp
      (eqRecRaTower_data ψ (hz ψ) ρ).1).1)
    (fun ψ ρ => ((bitAgree_wellDenotedV (bitAgree_eqRecValAV ψ) ρ).mp
      (eqRecRaTower_data ψ (hz ψ) ρ).1).2)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_ ?_
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact eqRecTy_wellDenotedV ψ (hz ψ) ρ
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [← AnnotTerm.BitAgree.interp_eq V (bitAgree_eqRecValAV ψ) ρ]
    exact (eqRecRaTower_data ψ (hz ψ) ρ).2
  · intro m₂ hac φ
    refine recRules_cons_rec mp hfresh eqRecA_eq m₂ hac φ ?_
    intro rl hrl _
    rcases List.mem_cons.mp hrl with rfl | hr'
    · exact eqRecLaw (m := mp.base2) m₂ hE hR hEv hRv hac φ
    · exact nomatch hr'

/-- **The `Eq` block, installed at the P tier.**  `BasisStepPB`'s
`eqK` branch — the block whose chain reads its own earlier leaves, and
so the one that consumes the install's exposed `acval`. -/
theorem declBasisPB_eqK {env₁ : Env} (mp : EnvModelM V μ env)
    (h : ConLeche.Semantics.BasisInstallRun env
      ConLeche.BasisKind.eqK.declsA env₁) :
    Nonempty (EnvModelM V μ env₁) := by
  rw [show ConLeche.BasisKind.eqK.declsA = [eqA, eqReflA, eqRecA]
    from rfl] at h
  obtain ⟨h1, h2, h3, hnil⟩ := h
  subst hnil
  have hf1 : env.find? eqName = none := Option.isNone_iff_eq_none.mp h1
  have hwf1 : EnvWF ⟨eqA :: env.consts⟩ :=
    EnvWF.cons mp.base2.wf ⟨rfl, rfl, rfl, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
  obtain ⟨mp1, hac1⟩ := extendEq mp hf1 hwf1
  have hEv1 : ∀ ψ : Name → Nat, mp1.base2.acval eqName ψ
      = eqValAV ψ := by
    intro ψ
    rw [hac1, show eqName = eqA.name from rfl, acvalWith_self]
  have hE1 : (⟨eqA :: env.consts⟩ : Env).find? eqName = some eqA := by
    rw [ConLeche.Env.find?_cons]; exact if_pos rfl
  have hf2 : (⟨eqA :: env.consts⟩ : Env).find? eqReflA.name = none :=
    Option.isNone_iff_eq_none.mp h2
  have hwf2 : EnvWF ⟨eqReflA :: eqA :: env.consts⟩ := by
    refine EnvWF.cons hwf1 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
    show Expr.constsResolve _ eqReflA.toConstantVal.type = true
    have hf : (⟨eqReflA :: eqA :: env.consts⟩ : Env).find? eqName
        = some eqA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hE1
    rw [show eqReflA.toConstantVal.type
        = Expr.forallE (.sort (.param uN))
            (Expr.forallE (.bvar 0)
              (.app (.app (.app (.const eqName [.param uN]) (.bvar 1))
                (.bvar 0)) (.bvar 0))
              { pw := .ifAllZero [] })
            { pw := .ifAllZero [] } from rfl]
    simp [Expr.constsResolve, hf]
  obtain ⟨mp2, hac2⟩ := extendEqRefl mp1 hE1 hEv1 hf2 hwf2
  have hE2 : (⟨eqReflA :: eqA :: env.consts⟩ : Env).find? eqName
      = some eqA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hE1
  have hR2 : (⟨eqReflA :: eqA :: env.consts⟩ : Env).find? eqReflName
      = some eqReflA := by
    rw [ConLeche.Env.find?_cons]; exact if_pos rfl
  have hEv2 : ∀ ψ : Name → Nat, mp2.base2.acval eqName ψ
      = eqValAV ψ := by
    intro ψ
    rw [hac2, acvalWith_ne (by decide)]
    exact hEv1 ψ
  have hRv2 : ∀ ψ : Name → Nat, mp2.base2.acval eqReflName ψ
      = eqReflValAV ψ := by
    intro ψ
    rw [hac2, show eqReflName = eqReflA.name from rfl, acvalWith_self]
  have hf3 : (⟨eqReflA :: eqA :: env.consts⟩ : Env).find?
      eqRecA.name = none := Option.isNone_iff_eq_none.mp h3
  have hwf3 : EnvWF ⟨eqRecA :: eqReflA :: eqA :: env.consts⟩ := by
    have hfE : (⟨eqRecA :: eqReflA :: eqA :: env.consts⟩ : Env).find?
        eqName = some eqA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hE2
    have hfR : (⟨eqRecA :: eqReflA :: eqA :: env.consts⟩ : Env).find?
        eqReflName = some eqReflA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hR2
    refine EnvWF.cons hwf2 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), ?_,
      (fun _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
    · show Expr.constsResolve _ eqRecA.toConstantVal.type = true
      rw [show eqRecA.toConstantVal.type
          = Expr.forallE (.sort (.param uN))
              (Expr.forallE (.bvar 0)
                (Expr.forallE
                  (Expr.forallE (.bvar 1)
                    (Expr.forallE
                      (.app (.app (.app (.const eqName [.param uN])
                        (.bvar 2)) (.bvar 1)) (.bvar 0))
                      (.sort (.param u1N))
                      { pw := .never })
                    { pw := .never })
                  (Expr.forallE
                    (.app (.app (.bvar 0) (.bvar 1))
                      (.app (.app (.const eqReflName [.param uN])
                        (.bvar 2)) (.bvar 1)))
                    (Expr.forallE (.bvar 3)
                      (Expr.forallE
                        (.app (.app (.app (.const eqName [.param uN])
                          (.bvar 4)) (.bvar 3)) (.bvar 0))
                        (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))
                        { pw := .ifAllZero [u1N] })
                      { pw := .ifAllZero [u1N] })
                    { pw := .ifAllZero [u1N] })
                  { pw := .ifAllZero [u1N] })
                { pw := .ifAllZero [u1N] })
              { pw := .ifAllZero [u1N] } from rfl]
      simp [Expr.constsResolve, hfE, hfR]
    · intro cv mI rP rules heq
      injection heq with h1' _ _ h4'
      subst h1'; subst h4'
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr'
      · exact ⟨rfl, rfl, by
          show Expr.constsResolve _ (RecRule.rhs eqRecRule) = true
          simp [Expr.constsResolve, eqRecRule, hfE, hfR], rfl,
          fun lvls pins heqf => nomatch heqf⟩
      · exact nomatch hr'
  obtain ⟨mp3, -⟩ := extendEqRec mp2 hE2 hR2 hEv2 hRv2 hf3 hwf3
  exact ⟨mp3⟩

end Eq

end ConLeche.Model
