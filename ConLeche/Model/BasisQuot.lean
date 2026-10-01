module

public import ConLeche.Model.BasisBlocks
import ConLeche.Semantics.BasisRules
/- `ConLeche.Kernel.PropWhen` seals its representation on purpose (the
`Std.HashMap` pattern, task #194): the datum's module is `public` but not
`@[expose]`d, so a `cases`-then-`rfl` proof cannot see the reduct.
`import all` restores that view HERE only. -/
import all ConLeche.Kernel.PropWhen

public section

/-!
# The `Quot` block, P tier (task #161, ENDGAME H)

The basis tier's fourth block, and the only one that

* stores an **axiom** (`Quot.sound` — the `hred` disjunct's second
  branch, unused by every earlier block), and
* reads a leaf that is **not** `pinnedStructT`: `Quot.lift`'s and
  `Quot.sound`'s stored types both mention the pinned `Eq` former,
  whose annotated leaf is the basis install's own tower.  Where v1
  crosses that gap with `EnvS.eq_lawV` (`quotInv_interpS` /
  `quotSoundTy_interpS`), the P tier crosses it with **`EqLaw`** —
  the `EnvModelM` field whose *supplier* is this very bundle, and whose
  grading half (v1 has no analogue: `AnnotOkV` has no bit content) is
  exactly what the reading's `htyOk` row needs.  The field is
  available at the `Quot` cons because `DeclBasisRun`'s first conjunct
  puts `Eq` in the prefix.

Everything else is the `BasisBlocksP.lean` recipe: five pinned
towers, five type readings, two `.plain` `RecRuleLaw` rows.  Both
recursors' motives land in `Sort 0`, so both rows are `Prop`-motive
rows and both fired equalities are the `PUnit.rec` observation seen
twice more — the reading's `lamR 0` and the value law's squash regime
are the same point.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule uN u1N vN)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

section Quot

open ConLeche (quotA quotMkA quotLiftA quotIndA quotSoundA quotName
  quotMkName quotLiftName quotIndName quotSoundName eqA eqName)

variable {m : EnvModel V env} {A : (Name → Nat) → AnnotTerm}

/-! ## The block's two pinned leaves

`Quot` and `Quot.mk` are read by every later constant in the block. -/

/-- The pinned `Quot` leaf at an extension, at any level. -/
theorem denoteMeta_quotLeaf {c₀ : ConstantInfo} (ψ : Name → Nat)
    (hne : ¬ c₀.name = quotName)
    (hQ : env.find? quotName = some quotA) (d : Nat) (l : Level) :
    denoteMeta (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d
        (.const quotName [l])
      = some (AnnotTerm.const .quot [l.eval ψ]) := by
  refine denoteMeta_pinned_const (m := m) hne hQ (by decide) (by rfl) ?_ d
  simp +decide [ConLeche.Verify.pinnedStructT]
  show Level.substFn ψ [uN] [l] uN = Level.eval ψ l
  simp [Level.substFn]

/-- The pinned `Quot.mk` leaf at an extension, at any level. -/
theorem denoteMeta_quotMkLeaf {c₀ : ConstantInfo} (ψ : Name → Nat)
    (hne : ¬ c₀.name = quotMkName)
    (hM : env.find? quotMkName = some quotMkA) (d : Nat) (l : Level) :
    denoteMeta (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d
        (.const quotMkName [l])
      = some (AnnotTerm.const .quotMk [l.eval ψ]) := by
  refine denoteMeta_pinned_const (m := m) hne hM (by decide) (by rfl) ?_ d
  simp +decide [ConLeche.Verify.pinnedStructT]
  show Level.substFn ψ [uN] [l] uN = Level.eval ψ l
  simp [Level.substFn]

/-! ## `Quot` and `Quot.mk` -/

/-- The relation binder's domain reading — shared by every constant in
the block, and `.never` at both of its own binders. -/
def quotRelTy : AnnotTerm :=
  .pi 0 1 (.bvar 0) (.pi 0 1 (.bvar 1) (.sort 0))

/-- **`Quot`'s type reading.** -/
theorem denoteMeta_quotA_type
    {acval : Name → (Name → Nat) → AnnotTerm} (ψ : Name → Nat) :
    denoteMeta acval ⟨quotA :: env.consts⟩ ψ 0 quotA.toConstantVal.type
      = some (.pi 0 (pwBit ψ .never) (.sort (ψ uN))
          (.pi 0 (pwBit ψ .never) (quotRelTy) (.sort (ψ uN)))) := by
  simp [quotA, ConstantInfo.toConstantVal, denoteMeta_forallE,
    denoteMeta_sort, denoteMeta_fvar, Expr.instantiate1, quotRelTy,
    pwBit_never, Level.eval, uN]

/-- **The `Quot` reading agrees with `BConst.typeAV`.**  Every binder in
the block's type formers is `.never`, so every numeral is `1` against a
successor or a `Nat.max _ 1`. -/
theorem bitAgree_quotRelTy (j : Nat) :
    AnnotTerm.BitAgree quotRelTy (relAV j (.bvar 0)) :=
  .pi (Iff.intro (fun h => absurd h Nat.one_ne_zero)
      (fun h => absurd h (maxOne_ne_zero j)))
    (.bvar 0) (.pi Iff.rfl (.bvar 1) (.sort 0))

theorem bitAgree_quotA (ψ : Name → Nat) :
    AnnotTerm.BitAgree
      (.pi 0 (pwBit ψ .never) (.sort (ψ uN))
        (.pi 0 (pwBit ψ .never) (quotRelTy) (.sort (ψ uN))))
      (BConst.typeAV .quot [ψ uN]) := by
  have h1 : pwBit ψ ConLeche.PropWhen.never = 0 ↔ ψ uN + 1 = 0 := by
    rw [pwBit_never]
    exact Iff.intro (fun h => nomatch h) (fun h => nomatch h)
  exact .pi h1 (.sort _) (.pi h1 (bitAgree_quotRelTy (ψ uN))
    (.sort _))

/-- `Quot.mk`'s type reading, named: three binders at the pin's bit. -/
def quotMkTy (b u : Nat) : AnnotTerm :=
  .pi 0 b (.sort u)
    (.pi 0 b quotRelTy
      (.pi 0 b (.bvar 1)
        (.app (.app (.const .quot [u]) (.bvar 2)) (.bvar 1))))

/-- **`Quot.mk`'s type reading.**  Stated at *any* extension whose cons
is neither `Quot` nor `Quot.mk` as well, because both recursor rows
read it as their fired constructor's telescope (`TVja`). -/
theorem denoteMeta_quotMkTy {c₀ : ConstantInfo} (ψ : Name → Nat)
    (hne : ¬ c₀.name = quotName)
    (hQ : env.find? quotName = some quotA) :
    denoteMeta (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ 0
        quotMkA.toConstantVal.type
      = some (quotMkTy (pwBit ψ (.ifAllZero [uN])) (ψ uN)) := by
  have hQc : ∀ d : Nat,
      denoteMeta (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d
        (Expr.const (Name.str Name.anonymous "Quot")
          [Level.param (Name.str Name.anonymous "u")])
        = some (AnnotTerm.const .quot
            [ψ (Name.str Name.anonymous "u")]) := by
    intro d
    exact denoteMeta_quotLeaf (m := m) (A := A) (c₀ := c₀) ψ hne hQ d
      (Level.param uN)
  simp [quotMkA, ConstantInfo.toConstantVal, denoteMeta_forallE,
    denoteMeta_sort, denoteMeta_app, denoteMeta_fvar, Expr.instantiate1,
    quotRelTy, quotMkTy, pwBit_never, hQc, Level.eval, uN]

theorem denoteMeta_quotMkA_type (ψ : Name → Nat)
    (hQ : env.find? quotName = some quotA) :
    denoteMeta (acvalWith m.acval quotMkA.name A)
        ⟨quotMkA :: env.consts⟩ ψ 0 quotMkA.toConstantVal.type
      = some (quotMkTy (pwBit ψ (.ifAllZero [uN])) (ψ uN)) :=
  denoteMeta_quotMkTy (m := m) (A := A) ψ (by decide) hQ

theorem bitAgree_quotMkA (ψ : Name → Nat) :
    AnnotTerm.BitAgree (quotMkTy (pwBit ψ (.ifAllZero [uN])) (ψ uN))
      (BConst.typeAV .quotMk [ψ uN]) := by
  have hz : pwBit ψ (ConLeche.PropWhen.ifAllZero [uN]) = 0 ↔ ψ uN = 0 :=
    pwBit_ifAllZero_single ψ uN
  rw [quotMkTy]
  exact .pi hz (.sort _)
    (.pi hz (bitAgree_quotRelTy (ψ uN))
      (.pi hz (.bvar 1)
        (.app (.app (.const _ _) (.bvar 2)) (.bvar 1))))

/-! ### The first two installs -/

/-- **`Quot`, installed at the P tier.** -/
theorem extendQuot (mp : EnvModelM V μ env)
    (hfresh : env.find? quotName = none)
    (hwf : EnvWF ⟨quotA :: env.consts⟩) :
    Nonempty (EnvModelM V μ ⟨quotA :: env.consts⟩) := by
  refine nonempty_of_exists (declStep_preserves_of_basis_cons mp
    (A := fun ψ => AnnotTerm.const .quot [ψ uN]) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT quotA.name ψ
          = some (Term.const .quot [ψ uN]) from rfl] at hp
        rw [← Option.some.inj hp]
        rfl)
      (fun _ h => nomatch h) (fun _ _ _ _ h => nomatch h))
    (fun _ _ => rfl) ?_
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, denoteMeta_quotA_type ψ⟩) ?_ ?_)
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [denoteMeta_quotA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact (bitAgree_wellDenotedV (bitAgree_quotA ψ) ρ).mpr
      (WellDenotedV_bconst_type V .quot [ψ uN] ρ)
  · intro ψ ta h ρ
    rw [denoteMeta_quotA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [AnnotTerm.BitAgree.interp_eq V (bitAgree_quotA ψ) ρ]
    exact bval_mem_type V .quot [ψ uN] ρ

/-- **`Quot.mk`, installed at the P tier.** -/
theorem extendQuotMk (mp : EnvModelM V μ env)
    (hQ : env.find? quotName = some quotA)
    (hfresh : env.find? quotMkName = none)
    (hwf : EnvWF ⟨quotMkA :: env.consts⟩) :
    Nonempty (EnvModelM V μ ⟨quotMkA :: env.consts⟩) := by
  have hty := fun ψ =>
    denoteMeta_quotMkA_type (m := mp.base2)
      (A := fun ψ => AnnotTerm.const .quotMk [ψ uN]) ψ hQ
  refine nonempty_of_exists (declStep_preserves_of_basis_cons mp
    (A := fun ψ => AnnotTerm.const .quotMk [ψ uN]) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT quotMkA.name ψ
          = some (Term.const .quotMk [ψ uN]) from rfl] at hp
        rw [← Option.some.inj hp]
        rfl)
      (fun _ h => nomatch h) (fun _ _ _ _ h => nomatch h))
    (fun _ _ => rfl) ?_
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_)
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact (bitAgree_wellDenotedV (bitAgree_quotMkA ψ) ρ).mpr
      (WellDenotedV_bconst_type V .quotMk [ψ uN] ρ)
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [AnnotTerm.BitAgree.interp_eq V (bitAgree_quotMkA ψ) ρ]
    exact bval_mem_type V .quotMk [ψ uN] ρ

/-! ## `Quot.ind`

The block's `Prop`-valued eliminator.  Every one of its binders is
pinned `.ifAllZero []`, so `pwBit_ifAllZero_nil` makes **every numeral
in the reading the literal `0`** — the reading is stated that way, and
the whole tower then lives in the squash regime.  `bval .quotInd` is
`pt` for the same reason (its result sort *is* `0`), so the row's
fired equality is `pt = pt` by `app_pt` and needs no value law at
all. -/

/-- `@Quot.{u} A r`, at two de Bruijn slots. -/
def quotApp (u i j : Nat) : AnnotTerm :=
  .app (.app (.const .quot [u]) (.bvar i)) (.bvar j)

/-- `@Quot.mk.{u} A r a`, at three de Bruijn slots. -/
def quotMkApp (u i j k : Nat) : AnnotTerm :=
  .app (.app (.app (.const .quotMk [u]) (.bvar i)) (.bvar j)) (.bvar k)

/-- `Quot.ind`'s motive binder domain reading. -/
def quotIndMotiveTy (u : Nat) : AnnotTerm :=
  .pi 0 1 (quotApp u 1 0) (.sort 0)

/-- `Quot.ind`'s minor binder domain reading. -/
def quotIndMinorTy (u : Nat) : AnnotTerm :=
  .pi 0 0 (.bvar 2) (.app (.bvar 1) (quotMkApp u 3 2 0))

/-- The motive space: `Quot A r → Prop`. -/
noncomputable def quotIndMotiveSpace (V : Type w) [SetTheory V]
    (u : Nat) (Aset R : V) : V :=
  piR 1 (quotSet u Aset R) fun _ => (univ 0 : V)

/-- The minor space: `∀ a, M (Quot.mk a)`. -/
noncomputable def quotIndMinorSpace (V : Type w) [SetTheory V]
    (u : Nat) (Aset R M : V) : V :=
  piR 0 Aset fun a => app M (quotClass u Aset R a)

/-! ### The two applied formers, graded and evaluated

`Quot A r` and `Quot.mk A r a` occur at four different de Bruijn
depths across the block, so both are stated against an arbitrary
environment through its slot values.  The `∃ w S F` witnesses are
`bconst_app_dataAV`/`_data3` — nothing is chosen. -/

theorem relAV_interp (u : Nat) (ρ : Nat → V) (Aset : V) :
    interp V (cons Aset ρ) (relAV u (.bvar 0)) = relSpace V u Aset := by
  simp [relAV, relSpace, AnnotTerm.lift, AnnotTerm.liftN, interp_pi,
    interp_bvar, interp_sort, cons]

theorem quotRelTy_interp (u : Nat) (ρ : Nat → V) (Aset : V) :
    interp V (cons Aset ρ) quotRelTy = relSpace V u Aset := by
  rw [← relAV_interp u ρ Aset]
  exact AnnotTerm.BitAgree.interp_eq V (bitAgree_quotRelTy u) _

/-- The relation binder's domain is graded, unconditionally: both of
its binders are in the graph regime. -/
theorem quotRelTy_wellDenotedV (ρ : Nat → V) : WellDenotedV V ρ quotRelTy :=
  ⟨⟨trivial, fun _ _ => ⟨trivial, fun _ _ => trivial⟩⟩,
    ⟨trivial,
      fun _ _ => ⟨trivial, fun _ _ => trivial,
        fun h => absurd h Nat.one_ne_zero⟩,
      fun h => absurd h Nat.one_ne_zero⟩⟩

theorem quotApp_data {u i j : Nat} {ρ : Nat → V} {Aset R : V}
    (hi : ρ i = Aset) (hj : ρ j = R)
    (hA : Aset ∈ˢ (univ u : V)) (hR : R ∈ˢ relSpace V u Aset) :
    WellDenoted V ρ (quotApp u i j) ∧ AnnotValid V ρ (quotApp u i j) ∧
      interp V ρ (quotApp u i j) = quotSet u Aset R := by
  have hAi : interp V ρ (AnnotTerm.bvar i) = Aset := by
    rw [interp_bvar, hi]
  have hRj : interp V ρ (AnnotTerm.bvar j) = R := by
    rw [interp_bvar, hj]
  have hA' : Aset ∈ˢ interp V ρ (AnnotTerm.sort u) := by
    rw [interp_sort]; exact hA
  have hR' : R ∈ˢ interp V (cons Aset ρ) (relAV u (.bvar 0)) := by
    rw [relAV_interp]; exact hR
  refine ⟨?_, ⟨⟨trivial, trivial⟩, trivial⟩, ?_⟩
  · rw [quotApp, WellDenoted_app]
    refine ⟨?_, trivial, ?_⟩
    · rw [WellDenoted_app]
      refine ⟨trivial, trivial, ?_⟩
      have h := bconst_app_data V .quot [u] ρ (A := .sort u) rfl hA'
      rw [← hAi] at h
      exact h
    · have h := bconst_app_dataAV V .quot [u] ρ
        (A := .sort u) (A2 := relAV u (.bvar 0)) rfl hA' hR'
      rw [← hAi, ← hRj] at h
      simpa [interp_const, bval, ConLeche.Term.lv] using h
  · rw [quotApp]
    simp only [interp_app, interp_const, bval, ConLeche.Term.lv,
      List.getD_cons_zero, hAi, hRj]
    exact quotV_app V hA hR

theorem quotMkApp_data {u i j k : Nat} {ρ : Nat → V} {Aset R a : V}
    (hi : ρ i = Aset) (hj : ρ j = R) (hk : ρ k = a)
    (hA : Aset ∈ˢ (univ u : V)) (hR : R ∈ˢ relSpace V u Aset)
    (ha : a ∈ˢ Aset) :
    WellDenoted V ρ (quotMkApp u i j k) ∧
      AnnotValid V ρ (quotMkApp u i j k) ∧
      interp V ρ (quotMkApp u i j k) = quotClass u Aset R a := by
  have hAi : interp V ρ (AnnotTerm.bvar i) = Aset := by
    rw [interp_bvar, hi]
  have hRj : interp V ρ (AnnotTerm.bvar j) = R := by
    rw [interp_bvar, hj]
  have hak : interp V ρ (AnnotTerm.bvar k) = a := by
    rw [interp_bvar, hk]
  have hA' : Aset ∈ˢ interp V ρ (AnnotTerm.sort u) := by
    rw [interp_sort]; exact hA
  have hR' : R ∈ˢ interp V (cons Aset ρ) (relAV u (.bvar 0)) := by
    rw [relAV_interp]; exact hR
  have ha' : a ∈ˢ interp V (cons R (cons Aset ρ)) (AnnotTerm.bvar 1) := by
    simpa [interp_bvar, cons] using ha
  refine ⟨?_, ⟨⟨⟨trivial, trivial⟩, trivial⟩, trivial⟩, ?_⟩
  · rw [quotMkApp, WellDenoted_app]
    refine ⟨?_, trivial, ?_⟩
    · rw [WellDenoted_app]
      refine ⟨?_, trivial, ?_⟩
      · rw [WellDenoted_app]
        refine ⟨trivial, trivial, ?_⟩
        have h := bconst_app_data V .quotMk [u] ρ (A := .sort u) rfl hA'
        rw [← hAi] at h
        exact h
      · have h := bconst_app_dataAV V .quotMk [u] ρ
          (A := .sort u) (A2 := relAV u (.bvar 0)) rfl hA' hR'
        rw [← hAi, ← hRj] at h
        simpa [interp_const, bval, ConLeche.Term.lv] using h
    · have h := bconst_app_data3 V .quotMk [u] ρ
        (A := .sort u) (A2 := relAV u (.bvar 0)) (A3 := .bvar 1)
        rfl hA' hR' ha'
      rw [← hAi, ← hRj, ← hak] at h
      simpa [interp_const, bval, ConLeche.Term.lv] using h
  · rw [quotMkApp]
    simp only [interp_app, interp_const, bval, ConLeche.Term.lv,
      List.getD_cons_zero, hAi, hRj, hak]
    exact quotMkV_app V hA hR ha

/-! ### The motive and minor spaces -/

theorem quotIndMotiveTy_interp {u : Nat} {Aset R : V} (ρ : Nat → V)
    (hA : Aset ∈ˢ (univ u : V)) (hR : R ∈ˢ relSpace V u Aset) :
    interp V (cons R (cons Aset ρ)) (quotIndMotiveTy u)
      = quotIndMotiveSpace V u Aset R := by
  rw [quotIndMotiveTy, interp_pi, quotIndMotiveSpace,
    (quotApp_data (u := u) (i := 1) (j := 0) (ρ := cons R (cons Aset ρ))
      (by simp [cons]) (by simp [cons]) hA hR).2.2]
  exact piR_congr fun _ _ => by rw [interp_sort]

theorem quotIndMinorTy_interp {u : Nat} {Aset R M : V} (ρ : Nat → V)
    (hA : Aset ∈ˢ (univ u : V)) (hR : R ∈ˢ relSpace V u Aset) :
    interp V (cons M (cons R (cons Aset ρ))) (quotIndMinorTy u)
      = quotIndMinorSpace V u Aset R M := by
  rw [quotIndMinorTy, interp_pi, quotIndMinorSpace]
  simp only [interp_bvar, cons]
  refine piR_congr fun a ha => ?_
  rw [interp_app,
    (quotMkApp_data (u := u) (i := 3) (j := 2) (k := 0)
      (ρ := cons a (cons M (cons R (cons Aset ρ))))
      (by simp [cons]) (by simp [cons]) (by simp [cons])
      hA hR ha).2.2]
  simp [interp_bvar, cons]

/-! ### The type reading -/

/-- `Quot.ind`'s type reading, named: five binders, every numeral the
literal `0`. -/
def quotIndTy (u : Nat) : AnnotTerm :=
  .pi 0 0 (.sort u)
    (.pi 0 0 quotRelTy
      (.pi 0 0 (quotIndMotiveTy u)
        (.pi 0 0 (quotIndMinorTy u)
          (.pi 0 0 (quotApp u 3 2) (.app (.bvar 2) (.bvar 0))))))

/-- **`Quot.ind`'s type reading.** -/
theorem denoteMeta_quotIndA_type (ψ : Name → Nat)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA) :
    denoteMeta (acvalWith m.acval quotIndA.name A)
        ⟨quotIndA :: env.consts⟩ ψ 0 quotIndA.toConstantVal.type
      = some (quotIndTy (ψ uN)) := by
  have hQc : ∀ d : Nat,
      denoteMeta (acvalWith m.acval quotIndA.name A)
        ⟨quotIndA :: env.consts⟩ ψ d (.const quotName [.param uN])
        = some (AnnotTerm.const .quot [ψ uN]) := fun d =>
    denoteMeta_quotLeaf (m := m) (A := A) ψ (by decide) hQ d
      (Level.param uN)
  have hMc : ∀ d : Nat,
      denoteMeta (acvalWith m.acval quotIndA.name A)
        ⟨quotIndA :: env.consts⟩ ψ d (.const quotMkName [.param uN])
        = some (AnnotTerm.const .quotMk [ψ uN]) := fun d =>
    denoteMeta_quotMkLeaf (m := m) (A := A) ψ (by decide) hM d
      (Level.param uN)
  rw [show quotIndA.toConstantVal.type
      = Expr.forallE (.sort (.param uN))
          (Expr.forallE
            (Expr.forallE (.bvar 0)
              (Expr.forallE (.bvar 1) (.sort .zero)
                { pw := .never })
              { pw := .never })
            (Expr.forallE
              (Expr.forallE
                (.app (.app (.const quotName [.param uN]) (.bvar 1))
                  (.bvar 0)) (.sort .zero)
                { pw := .never })
              (Expr.forallE
                (Expr.forallE (.bvar 2)
                  (.app (.bvar 1)
                    (.app (.app (.app (.const quotMkName [.param uN])
                      (.bvar 3)) (.bvar 2)) (.bvar 0)))
                  { pw := .ifAllZero [] })
                (Expr.forallE
                  (.app (.app (.const quotName [.param uN]) (.bvar 3))
                    (.bvar 2))
                  (.app (.bvar 2) (.bvar 0))
                  { pw := .ifAllZero [] })
                { pw := .ifAllZero [] })
              { pw := .ifAllZero [] })
            { pw := .ifAllZero [] })
          { pw := .ifAllZero [] } from rfl]
  simp [denoteMeta_forallE, denoteMeta_sort, denoteMeta_app, denoteMeta_fvar,
    Expr.instantiate1, quotRelTy, quotApp, quotMkApp,
    quotIndMotiveTy, quotIndMinorTy, quotIndTy, pwBit_never,
    pwBit_ifAllZero_nil, hQc, hMc, Level.eval]

theorem bitAgree_quotIndA (ψ : Name → Nat) :
    AnnotTerm.BitAgree (quotIndTy (ψ uN))
      (BConst.typeAV .quotInd [ψ uN]) :=
  .pi Iff.rfl (.sort _)
    (.pi Iff.rfl (bitAgree_quotRelTy (ψ uN))
      (.pi Iff.rfl
        (.pi Iff.rfl (.app (.app (.const _ _) (.bvar 1)) (.bvar 0))
          (.sort 0))
        (.pi Iff.rfl
          (.pi Iff.rfl (.bvar 2)
            (.app (.bvar 1)
              (.app (.app (.app (.const _ _) (.bvar 3)) (.bvar 2))
                (.bvar 0))))
          (.pi Iff.rfl (.app (.app (.const _ _) (.bvar 3)) (.bvar 2))
            (.app (.bvar 2) (.bvar 0))))))

/-! ### The squash-regime kit

Everything `Quot.ind` builds — its tower, its rule's right-hand side,
and every application of either — lives at bit `0`, where `lamR` is
`pt` and a fibre only has to be an inhabited truth value.  These three
lemmas are that observation, stated once; `Quot.sound` and (at the
`PSigma'` block) `PSigma'.rec` read them too. -/

/-- The inhabited truth value a squash-regime tower's grading picks for
its fibre: `True`, as a `piR 0`. -/
noncomputable def unitPropR (V : Type w) [SetTheory V] : V :=
  piR 0 (unitSet : V) fun _ => unitSet

theorem unitPropR_mem_univZero : unitPropR V ∈ˢ (univZero : V) :=
  piR_zero_mem_univZero

theorem pt_mem_unitPropR : (pt : V) ∈ˢ unitPropR V :=
  pt_mem_piR_zero fun _ _ => ⟨pt, pt_mem_unitSet⟩

/-- **A squash-regime `λ` whose body is the canonical proof is graded**
— the fibre is `unitPropR`, and both of `WellDenoted`'s residual
obligations are its two facts. -/
theorem WellDenotedV_lam_zero_pt {ρ : Nat → V} {Aa b : AnnotTerm}
    (hA : WellDenotedV V ρ Aa)
    (hb : ∀ x, x ∈ˢ interp V ρ Aa → WellDenotedV V (cons x ρ) b)
    (hpt : ∀ x, x ∈ˢ interp V ρ Aa → interp V (cons x ρ) b = pt) :
    WellDenotedV V ρ (.lam 0 Aa b) := by
  refine ⟨?_, ?_⟩
  · rw [WellDenoted_lam]
    exact ⟨hA.1, fun x hx => (hb x hx).1, fun _ => unitPropR V,
      fun x hx => by rw [hpt x hx]; exact pt_mem_unitPropR,
      fun _ x _ => unitPropR_mem_univZero⟩
  · rw [AnnotValid_lam]
    exact ⟨hA.2, fun x hx => (hb x hx).2⟩

/-- **The canonical proof applied to anything is graded, and is again
the canonical proof.**  The `∃ w S F` witness is `w = 0`, the
argument's own domain, and the constant `unitPropR` fibre. -/
theorem WellDenotedV_app_pt {ρ : Nat → V} {f a : AnnotTerm} {S : V}
    (hf : WellDenotedV V ρ f) (hfi : interp V ρ f = pt)
    (ha : WellDenotedV V ρ a) (hmem : interp V ρ a ∈ˢ S) :
    WellDenotedV V ρ (.app f a) ∧ interp V ρ (.app f a) = pt := by
  refine ⟨⟨?_, ⟨hf.2, ha.2⟩⟩, by rw [interp_app, hfi, app_pt]⟩
  rw [WellDenoted_app]
  exact ⟨hf.1, ha.1, 0, S, fun _ => unitPropR V,
    by rw [hfi]; exact pt_mem_piR_zero fun _ _ => ⟨pt, pt_mem_unitPropR⟩,
    hmem, fun _ _ _ => unitPropR_mem_univZero⟩

/-! ### The two domains, graded -/

theorem quotIndMotiveTy_wellDenotedV {u : Nat} {Aset R : V} (ρ : Nat → V)
    (hA : Aset ∈ˢ (univ u : V)) (hR : R ∈ˢ relSpace V u Aset) :
    WellDenotedV V (cons R (cons Aset ρ)) (quotIndMotiveTy u) := by
  obtain ⟨hok, hval, -⟩ := quotApp_data (u := u) (i := 1) (j := 0)
    (ρ := cons R (cons Aset ρ)) (by simp [cons]) (by simp [cons]) hA hR
  exact ⟨⟨hok, fun _ _ => trivial⟩,
    ⟨hval, fun _ _ => trivial, fun h => absurd h Nat.one_ne_zero⟩⟩

theorem quotIndMinorTy_wellDenotedV {u : Nat} {Aset R M : V} (ρ : Nat → V)
    (hA : Aset ∈ˢ (univ u : V)) (hR : R ∈ˢ relSpace V u Aset)
    (hM : M ∈ˢ quotIndMotiveSpace V u Aset R) :
    WellDenotedV V (cons M (cons R (cons Aset ρ))) (quotIndMinorTy u) := by
  have hdom : interp V (cons M (cons R (cons Aset ρ)))
      (AnnotTerm.bvar 2) = Aset := by simp [interp_bvar, cons]
  have hstep : ∀ a : V, a ∈ˢ Aset →
      (WellDenoted V (cons a (cons M (cons R (cons Aset ρ))))
          (.app (.bvar 1) (quotMkApp u 3 2 0)) ∧
        AnnotValid V (cons a (cons M (cons R (cons Aset ρ))))
          (.app (.bvar 1) (quotMkApp u 3 2 0))) ∧
      interp V (cons a (cons M (cons R (cons Aset ρ))))
        (.app (.bvar 1) (quotMkApp u 3 2 0))
          ∈ˢ (univZero : V) := by
    intro a ha
    obtain ⟨hok, hval, hint⟩ := quotMkApp_data (u := u)
      (i := 3) (j := 2) (k := 0)
      (ρ := cons a (cons M (cons R (cons Aset ρ))))
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hA hR ha
    have hMb : interp V (cons a (cons M (cons R (cons Aset ρ))))
        (AnnotTerm.bvar 1) = M := by simp [interp_bvar, cons]
    have hcl : quotClass u Aset R a ∈ˢ quotSet u Aset R :=
      quotClass_mem ha
    have hMc : app M (quotClass u Aset R a) ∈ˢ (univ 0 : V) :=
      app_mem_piR_pos (A := quotSet u Aset R)
        (B := fun _ => (univ 0 : V)) Nat.one_ne_zero hM hcl
    refine ⟨⟨?_, ⟨trivial, hval⟩⟩, ?_⟩
    · rw [WellDenoted_app]
      exact ⟨trivial, hok, 1, quotSet u Aset R, fun _ => (univ 0 : V),
        by rw [hMb]; exact hM, by rw [hint]; exact hcl,
        fun h => absurd h Nat.one_ne_zero⟩
    · rw [interp_app, hMb, hint, ← univ_zero]
      exact hMc
  exact ⟨⟨trivial, fun a ha => (hstep a (by rwa [hdom] at ha)).1.1⟩,
    ⟨trivial, fun a ha => (hstep a (by rwa [hdom] at ha)).1.2,
      fun _ a ha => (hstep a (by rwa [hdom] at ha)).2⟩⟩

/-! ### The rule, its right-hand side, and the row -/

/-- `Quot.ind`'s rule's RHS reading. -/
def quotIndRa (u : Nat) : AnnotTerm :=
  .lam 0 (.sort u)
    (.lam 0 quotRelTy
      (.lam 0 (quotIndMotiveTy u)
        (.lam 0 (quotIndMinorTy u)
          (.lam 0 (.bvar 3) (.app (.bvar 1) (.bvar 0))))))

theorem quotIndRa_interp (u : Nat) (ρ : Nat → V) :
    interp V ρ (quotIndRa u) = (pt : V) := by
  rw [quotIndRa, interp_lam, lamR_zero]

/-- **`Quot.ind`'s RHS tower is graded** — five squash-regime `λ`s
whose bodies are all the canonical proof (the innermost because the
minor premise itself is, by `eq_pt_of_mem_piR_zero` on its
`Prop`-valued product). -/
theorem quotIndRa_wellDenotedV (u : Nat) (ρ : Nat → V) :
    WellDenotedV V ρ (quotIndRa u) := by
  rw [quotIndRa]
  refine WellDenotedV_lam_zero_pt ⟨trivial, trivial⟩ ?_
    (fun _ _ => by rw [interp_lam, lamR_zero])
  intro Aset hAset
  rw [interp_sort] at hAset
  refine WellDenotedV_lam_zero_pt (quotRelTy_wellDenotedV _) ?_
    (fun _ _ => by rw [interp_lam, lamR_zero])
  intro R hR
  rw [quotRelTy_interp u] at hR
  refine WellDenotedV_lam_zero_pt (quotIndMotiveTy_wellDenotedV ρ hAset hR) ?_
    (fun _ _ => by rw [interp_lam, lamR_zero])
  intro M hM
  rw [quotIndMotiveTy_interp ρ hAset hR] at hM
  refine WellDenotedV_lam_zero_pt (quotIndMinorTy_wellDenotedV ρ hAset hR hM) ?_
    (fun _ _ => by rw [interp_lam, lamR_zero])
  intro mk hmk
  rw [quotIndMinorTy_interp ρ hAset hR, quotIndMinorSpace] at hmk
  have hmkpt : mk = pt := eq_pt_of_mem_piR_zero hmk
  have hdom : interp V (cons mk (cons M (cons R (cons Aset ρ))))
      (AnnotTerm.bvar 3) = Aset := by simp [interp_bvar, cons]
  have hbody : ∀ a : V, a ∈ˢ Aset →
      WellDenotedV V (cons a (cons mk (cons M (cons R (cons Aset ρ)))))
          (.app (.bvar 1) (.bvar 0)) ∧
        interp V (cons a (cons mk (cons M (cons R (cons Aset ρ)))))
          (.app (.bvar 1) (.bvar 0)) = pt := by
    intro a ha
    refine WellDenotedV_app_pt (S := Aset) ⟨trivial, trivial⟩ ?_
      ⟨trivial, trivial⟩ ?_
    · rw [interp_bvar]
      show cons a (cons mk (cons M (cons R (cons Aset ρ)))) 1 = pt
      rw [show cons a (cons mk (cons M (cons R (cons Aset ρ)))) 1
        = mk from rfl]
      exact hmkpt
    · rw [interp_bvar]
      exact ha
  refine WellDenotedV_lam_zero_pt ⟨trivial, trivial⟩ ?_ ?_
  · exact fun a ha => (hbody a (by rwa [hdom] at ha)).1
  · exact fun a ha => (hbody a (by rwa [hdom] at ha)).2

/-- **`Quot.ind`'s rule's RHS reading.** -/
theorem denoteMeta_quotInd_rhs (ψ : Name → Nat)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA) :
    denoteMeta (acvalWith m.acval quotIndA.name A)
        ⟨quotIndA :: env.consts⟩ ψ 0 quotIndRule.rhs
      = some (quotIndRa (ψ uN)) := by
  have hQc : ∀ d : Nat,
      denoteMeta (acvalWith m.acval quotIndA.name A)
        ⟨quotIndA :: env.consts⟩ ψ d (.const quotName [.param uN])
        = some (AnnotTerm.const .quot [ψ uN]) := fun d =>
    denoteMeta_quotLeaf (m := m) (A := A) ψ (by decide) hQ d
      (Level.param uN)
  have hMc : ∀ d : Nat,
      denoteMeta (acvalWith m.acval quotIndA.name A)
        ⟨quotIndA :: env.consts⟩ ψ d (.const quotMkName [.param uN])
        = some (AnnotTerm.const .quotMk [ψ uN]) := fun d =>
    denoteMeta_quotMkLeaf (m := m) (A := A) ψ (by decide) hM d
      (Level.param uN)
  simp only [quotIndRule]
  simp [denoteMeta_lam, denoteMeta_forallE, denoteMeta_sort, denoteMeta_app,
    denoteMeta_fvar, Expr.instantiate1, quotRelTy, quotApp, quotMkApp,
    quotIndMotiveTy, quotIndMinorTy, quotIndRa, pwBit_never,
    pwBit_ifAllZero_nil, hQc, hMc, Level.eval]

/-- **`Quot.ind`'s `RecRuleLaw` row.**  The rule is `.plain`, so both
`.nested` conjuncts are `nomatch`; the fired equality is `pt = pt`
(`bval .quotInd` is the canonical proof and so is the RHS tower), and
the transport is five `WellDenotedV_app_pt` steps whose domains come
straight off the two telescope fits — no domain has to be
identified. -/
theorem quotIndLaw {m : EnvModel V env}
    (m₂ : EnvModel V ⟨quotIndA :: env.consts⟩)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hac : m₂.acval = acvalWith m.acval quotIndA.name
      (fun ψ => AnnotTerm.const .quotInd [ψ uN]))
    (φ : Name → Nat) :
    RecRuleLaw m₂ φ quotIndA.name quotIndA.toConstantVal 4 4
      quotIndRule := by
  refine ⟨Nat.le_refl 4, fun us hus => ?_⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Name → Nat,
      ψ = Level.substFn φ quotIndA.toConstantVal.levelParams us :=
    ⟨_, rfl⟩
  have hRa : denoteMeta m₂.acval ⟨quotIndA :: env.consts⟩ φ 0
      (quotIndRule.rhs.instantiateLevelParams
        quotIndA.toConstantVal.levelParams us)
      = some (quotIndRa (ψ uN)) := by
    rw [denoteMeta_instLevels (acvalParamsAt_of_core m₂) φ, hac, hψ,
      denoteMeta_quotInd_rhs (m := m) _ hQ hM]
  refine ⟨quotIndRa (ψ uN), hRa, fun ρ => quotIndRa_wellDenotedV _ ρ, ?_, ?_⟩
  · intro _ _ h
    exact nomatch h
  intro cvj cnP cnF hfj usj ρ xs ys TVa TVja restR restC hxs hys husj
    hlev _ hnested hpin hTVa hTVja hfitR hfitC
  -- the fired constructor is `Quot.mk`, stored in the prefix
  have hM' : (⟨quotIndA :: env.consts⟩ : Env).find? quotMkName
      = some quotMkA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hM
  rw [show RecRule.ctor quotIndRule = quotMkName from rfl, hM'] at hfj
  obtain ⟨rfl, rfl, rfl⟩ :
      cvj = quotMkA.toConstantVal ∧ cnP = 2 ∧ cnF = 1 := by
    injection Option.some.inj hfj with a1 a2 a3
    exact ⟨a1.symm, a2.symm, a3.symm⟩
  obtain ⟨x1, x2, x3, x4, rfl⟩ : ∃ p q r s, xs = [p, q, r, s] := by
    match xs, hxs with
    | [p, q, r, s], _ => exact ⟨p, q, r, s, rfl⟩
  obtain ⟨y1, y2, y3, rfl⟩ : ∃ p q r, ys = [p, q, r] := by
    match ys, hys with
    | [p, q, r], _ => exact ⟨p, q, r, rfl⟩
  have hTyRead : denoteMeta m₂.acval ⟨quotIndA :: env.consts⟩ φ 0
      (quotIndA.toConstantVal.type.instantiateLevelParams
        quotIndA.toConstantVal.levelParams us)
      = some (quotIndTy (ψ uN)) := by
    rw [denoteMeta_instLevels (acvalParamsAt_of_core m₂) φ, hac,
      denoteMeta_quotIndA_type (m := m) _ hQ hM, ← hψ]
  obtain rfl : TVa = _ :=
    (Option.some.inj (hTyRead.symm.trans hTVa)).symm
  have hCtorRead : denoteMeta m₂.acval ⟨quotIndA :: env.consts⟩ φ 0
      (quotMkA.toConstantVal.type.instantiateLevelParams
        quotMkA.toConstantVal.levelParams usj)
      = some (quotMkTy
          (pwBit (Level.substFn φ quotMkA.toConstantVal.levelParams usj)
            (.ifAllZero [uN]))
          (Level.substFn φ quotMkA.toConstantVal.levelParams usj uN)) := by
    rw [denoteMeta_instLevels (acvalParamsAt_of_core m₂) φ, hac,
      denoteMeta_quotMkTy (m := m) _ (by decide) hQ]
  obtain rfl : TVja = _ :=
    (Option.some.inj (hCtorRead.symm.trans hTVja)).symm
  have hrecL : m₂.acval quotIndA.name
      (Level.substFn φ quotIndA.toConstantVal.levelParams us)
      = AnnotTerm.const .quotInd [ψ uN] := by
    rw [hac, acvalWith_self, hψ]
  rw [quotIndTy] at hfitR
  rw [quotMkTy] at hfitC
  cases hfitR with | cons f1 hfitR =>
  cases hfitR with | cons f2 hfitR =>
  cases hfitR with | cons f3 hfitR =>
  cases hfitR with | cons f4 hfitR =>
  cases hfitR with | cons f5 _ =>
  cases hfitC with | cons g1 hfitC =>
  cases hfitC with | cons g2 hfitC =>
  cases hfitC with | cons g3 _ =>
  refine ⟨?_, ?_⟩
  · -- the fired equality: both sides are the canonical proof
    simp only [show RecRule.ctor quotIndRule = quotMkName from rfl,
      show quotIndRule.ctorParams = 2 from rfl,
      List.take, List.drop, List.cons_append, List.nil_append,
      AnnotTerm.mkAppN_cons, AnnotTerm.mkAppN_nil,
      hrecL, interp_app, interp_const, bval, quotIndRa_interp,
      app_pt]
  · -- the transport: five squash-regime applications
    intro hxsA hysA
    simp only [show quotIndRule.ctorParams = 2 from rfl,
      List.take, List.drop, List.cons_append, List.nil_append,
      AnnotTerm.mkAppN_cons, AnnotTerm.mkAppN_nil]
    have h1 := WellDenotedV_app_pt (quotIndRa_wellDenotedV (ψ uN) ρ)
      (quotIndRa_interp (ψ uN) ρ) (hxsA x1 (by simp)) f1
    have h2 := WellDenotedV_app_pt h1.1 h1.2 (hxsA x2 (by simp)) f2
    have h3 := WellDenotedV_app_pt h2.1 h2.2 (hxsA x3 (by simp)) f3
    have h4 := WellDenotedV_app_pt h3.1 h3.2 (hxsA x4 (by simp)) f4
    exact (WellDenotedV_app_pt h4.1 h4.2 (hysA y3 (by simp)) g3).1

/-- **`Quot.ind`, installed at the P tier.** -/
theorem extendQuotInd (mp : EnvModelM V μ env)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hfresh : env.find? quotIndA.name = none)
    (hwf : EnvWF ⟨quotIndA :: env.consts⟩) :
    Nonempty (EnvModelM V μ ⟨quotIndA :: env.consts⟩) := by
  have hty := fun ψ =>
    denoteMeta_quotIndA_type (m := mp.base2)
      (A := fun ψ => AnnotTerm.const .quotInd [ψ uN]) ψ hQ hM
  refine nonempty_of_exists (declStep_preserves_of_basis_rec_cons mp
    (A := fun ψ => AnnotTerm.const .quotInd [ψ uN]) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT quotIndA.name ψ
          = some (Term.const .quotInd [ψ uN]) from rfl] at hp
        rw [← Option.some.inj hp]
        rfl)
      (fun _ h => nomatch h)
      (fun _ _ _ _ heq r hr => by
        injection heq with _ _ _ h4
        rw [← h4] at hr
        rcases List.mem_cons.mp hr with rfl | hr'
        · exact ⟨⟨_, _, _, hM⟩, fun hb => Bool.noConfusion hb,
            fun hb => Bool.noConfusion hb⟩
        · exact nomatch hr'))
    (fun _ _ => rfl) ?_
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_ ?_)
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact (bitAgree_wellDenotedV (bitAgree_quotIndA ψ) ρ).mpr
      (WellDenotedV_bconst_type V .quotInd [ψ uN] ρ)
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [AnnotTerm.BitAgree.interp_eq V (bitAgree_quotIndA ψ) ρ]
    exact bval_mem_type V .quotInd [ψ uN] ρ
  · intro m₂ hac φ
    refine recRules_cons_rec mp hfresh quotIndA_eq m₂ hac φ ?_
    intro rl hrl _
    rcases List.mem_cons.mp hrl with rfl | hr'
    · exact quotIndLaw (m := mp.base2) m₂ hQ hM hac φ
    · exact nomatch hr'

/-! ## The `Eq` bridge

`Quot.sound`'s and `Quot.lift`'s stored types conclude at the pinned
`Eq` former, whose annotated leaf is **not** `pinnedStructT` (the
ENDGAME D finding) — it is the basis install's own tower.  v1 crosses
the gap with `EnvS.eq_lawV`; here the crossing is `EqLaw`, the
`EnvModelM` field this very bundle supplies, and it crosses **both**
halves at once: its value half computes the spine, and its grading
half — which v1 has no analogue for, because `AnnotOkV` has no bit
content — is exactly the reading's `htyOk` obligation at that slot.

Both consumers below take the two halves as plain hypotheses at the
level the constant reads `Eq` at, so neither mentions `EnvModelM`. -/

/-- The stored `Eq` former's leaf at a `Quot`-block extension: the
prefix's own, by `acvalWith_ne`. -/
theorem denoteMeta_eqLeaf {c₀ : ConstantInfo} (ψ : Name → Nat) (l : Level)
    (hne : ¬ c₀.name = eqName)
    (hE : env.find? eqName = some eqA) (d : Nat) :
    denoteMeta (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d
        (.const eqName [l])
      = some (m.acval eqName (Level.substFn ψ [uN] [l])) := by
  have hf' : (⟨c₀ :: env.consts⟩ : Env).find? eqName = some eqA := by
    rw [ConLeche.Env.find?_cons, if_neg hne]; exact hE
  rw [denoteMeta_const hf' (by rfl), acvalWith_ne (fun h => hne h.symm)]
  rfl

/-- The relation, applied to two of its arguments. -/
theorem relApp_data {u i j k : Nat} {ρ : Nat → V} {Aset R a b : V}
    (hi : ρ i = R) (hj : ρ j = a) (hk : ρ k = b)
    (hR : R ∈ˢ relSpace V u Aset) (ha : a ∈ˢ Aset) (hb : b ∈ˢ Aset) :
    WellDenoted V ρ (.app (.app (.bvar i) (.bvar j)) (.bvar k)) ∧
      AnnotValid V ρ (.app (.app (.bvar i) (.bvar j)) (.bvar k)) ∧
      interp V ρ (.app (.app (.bvar i) (.bvar j)) (.bvar k))
        = app (app R a) b := by
  have hRi : interp V ρ (AnnotTerm.bvar i) = R := by rw [interp_bvar, hi]
  have haj : interp V ρ (AnnotTerm.bvar j) = a := by rw [interp_bvar, hj]
  have hbk : interp V ρ (AnnotTerm.bvar k) = b := by rw [interp_bvar, hk]
  have hR' : R ∈ˢ piR (Nat.max u 1) Aset
      (fun _ => piR 1 Aset fun _ => (univ 0 : V)) := hR
  have hRa : app R a ∈ˢ piR 1 Aset fun _ => (univ 0 : V) :=
    app_mem_piR_pos (maxOne_ne_zero u) hR' ha
  refine ⟨?_, ⟨⟨trivial, trivial⟩, trivial⟩, ?_⟩
  · rw [WellDenoted_app]
    refine ⟨?_, trivial, 1, Aset, fun _ => (univ 0 : V), ?_, ?_,
      fun h => absurd h Nat.one_ne_zero⟩
    · rw [WellDenoted_app]
      exact ⟨trivial, trivial, Nat.max u 1, Aset,
        fun _ => piR 1 Aset fun _ => (univ 0 : V),
        by rw [hRi]; exact hR',
        by rw [haj]; exact ha,
        fun h => absurd h (maxOne_ne_zero u)⟩
    · rw [interp_app, hRi, haj]; exact hRa
    · rw [hbk]; exact hb
  · rw [interp_app, interp_app, hRi, haj, hbk]

/-! ## `Quot.sound`

The block's stored axiom, and the basis blocks' only one: its
`reduce_ops` row is the `hred` disjunct's second branch (`Quot.sound`
is not a trusted operation), unused by every earlier block.  Its type
is `Prop`-valued throughout, so the membership obligation is `pt` in a
five-deep `piR 0` — five `pt_mem_piR_zero` steps whose innermost
witness is the quotient's own soundness. -/

/-- `Quot.sound`'s type reading, named. -/
def quotSoundTy (E : AnnotTerm) (u : Nat) : AnnotTerm :=
  .pi 0 0 (.sort u)
    (.pi 0 0 quotRelTy
      (.pi 0 0 (.bvar 1)
        (.pi 0 0 (.bvar 2)
          (.pi 0 0 (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
            (.app (.app (.app E (quotApp u 4 3))
              (quotMkApp u 4 3 2)) (quotMkApp u 4 3 1))))))

/-- **`Quot.sound`'s type reading.** -/
theorem denoteMeta_quotSoundA_type (ψ : Name → Nat)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hE : env.find? eqName = some eqA) :
    denoteMeta (acvalWith m.acval quotSoundA.name A)
        ⟨quotSoundA :: env.consts⟩ ψ 0 quotSoundA.toConstantVal.type
      = some (quotSoundTy (m.acval eqName ψ) (ψ uN)) := by
  have hQc : ∀ d : Nat,
      denoteMeta (acvalWith m.acval quotSoundA.name A)
        ⟨quotSoundA :: env.consts⟩ ψ d (.const quotName [.param uN])
        = some (AnnotTerm.const .quot [ψ uN]) := fun d =>
    denoteMeta_quotLeaf (m := m) (A := A) ψ (by decide) hQ d
      (Level.param uN)
  have hMc : ∀ d : Nat,
      denoteMeta (acvalWith m.acval quotSoundA.name A)
        ⟨quotSoundA :: env.consts⟩ ψ d (.const quotMkName [.param uN])
        = some (AnnotTerm.const .quotMk [ψ uN]) := fun d =>
    denoteMeta_quotMkLeaf (m := m) (A := A) ψ (by decide) hM d
      (Level.param uN)
  have hEc : ∀ d : Nat,
      denoteMeta (acvalWith m.acval quotSoundA.name A)
        ⟨quotSoundA :: env.consts⟩ ψ d (.const eqName [.param uN])
        = some (m.acval eqName ψ) := by
    intro d
    rw [denoteMeta_eqLeaf (m := m) (A := A) ψ (Level.param uN)
      (by decide) hE d,
      show ([Level.param uN] : List Level)
        = List.map Level.param [uN] from rfl,
      Level.substFn_param_self ψ [uN]]
  rw [show quotSoundA.toConstantVal.type
      = Expr.forallE (.sort (.param uN))
          (Expr.forallE
            (Expr.forallE (.bvar 0)
              (Expr.forallE (.bvar 1) (.sort .zero)
                { pw := .never })
              { pw := .never })
            (Expr.forallE (.bvar 1)
              (Expr.forallE (.bvar 2)
                (Expr.forallE
                  (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
                  (.app (.app (.app (.const eqName [.param uN])
                    (.app (.app (.const quotName [.param uN]) (.bvar 4))
                      (.bvar 3)))
                    (.app (.app (.app (.const quotMkName [.param uN])
                      (.bvar 4)) (.bvar 3)) (.bvar 2)))
                    (.app (.app (.app (.const quotMkName [.param uN])
                      (.bvar 4)) (.bvar 3)) (.bvar 1)))
                  { pw := .ifAllZero [] })
                { pw := .ifAllZero [] })
              { pw := .ifAllZero [] })
            { pw := .ifAllZero [] })
          { pw := .ifAllZero [] } from rfl]
  simp [denoteMeta_forallE, denoteMeta_sort, denoteMeta_app, denoteMeta_fvar,
    Expr.instantiate1, quotRelTy, quotApp, quotMkApp, quotSoundTy,
    pwBit_never, pwBit_ifAllZero_nil, hQc, hMc, hEc, Level.eval]

/-- **A `Prop`-valued product's grading step**, stated so the five
binders of `Quot.sound`'s type (and the three of `Quot.lift`'s
invariance premise) are five applications of one lemma: the product is
graded and *is itself* a truth value, which is exactly what the next
binder out needs. -/
theorem WellDenotedV_pi_zero {ρ : Nat → V} {Aa B : AnnotTerm}
    (hA : WellDenotedV V ρ Aa)
    (hB : ∀ x, x ∈ˢ interp V ρ Aa → WellDenotedV V (cons x ρ) B)
    (hz : ∀ x, x ∈ˢ interp V ρ Aa →
      interp V (cons x ρ) B ∈ˢ (univZero : V)) :
    WellDenotedV V ρ (.pi 0 0 Aa B) ∧
      interp V ρ (.pi 0 0 Aa B) ∈ˢ (univZero : V) := by
  refine ⟨⟨⟨hA.1, fun x hx => (hB x hx).1⟩,
    ⟨hA.2, fun x hx => (hB x hx).2, fun _ x hx => hz x hx⟩⟩, ?_⟩
  rw [interp_pi]
  exact piR_zero_mem_univZero

/-- **`Quot.sound`'s type reading is graded** — five
`WellDenotedV_pi_zero` steps whose innermost slot is `EqLaw`'s grading
half. -/
theorem quotSoundTy_wellDenotedV {E : AnnotTerm} {u : Nat} (ρ : Nat → V)
    (hgr : ∀ (ρ' : Nat → V) (Aa la ra : AnnotTerm),
      WellDenotedV V ρ' Aa → WellDenotedV V ρ' la → WellDenotedV V ρ' ra →
      interp V ρ' Aa ∈ˢ (univ u : V) →
      interp V ρ' la ∈ˢ interp V ρ' Aa →
      interp V ρ' ra ∈ˢ interp V ρ' Aa →
      WellDenotedV V ρ' (.app (.app (.app E Aa) la) ra) ∧
        interp V ρ' (.app (.app (.app E Aa) la) ra)
          ∈ˢ (univZero : V)) :
    WellDenotedV V ρ (quotSoundTy E u) := by
  -- the innermost slot: `EqLaw`'s grading half at the three spine
  -- arguments, whose readings are the block's two applied formers
  have hin : ∀ Aset R a b w : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace V u Aset → a ∈ˢ Aset → b ∈ˢ Aset →
      WellDenotedV V (cons w (cons b (cons a (cons R (cons Aset ρ)))))
          (.app (.app (.app E (quotApp u 4 3)) (quotMkApp u 4 3 2))
            (quotMkApp u 4 3 1)) ∧
        interp V (cons w (cons b (cons a (cons R (cons Aset ρ)))))
          (.app (.app (.app E (quotApp u 4 3)) (quotMkApp u 4 3 2))
            (quotMkApp u 4 3 1)) ∈ˢ (univZero : V) := by
    intro Aset R a b w hAset hR ha hb
    obtain ⟨hTok, hTval, hTint⟩ := quotApp_data (u := u) (i := 4) (j := 3)
      (ρ := cons w (cons b (cons a (cons R (cons Aset ρ)))))
      (by simp [cons]) (by simp [cons]) hAset hR
    obtain ⟨hlok, hlval, hlint⟩ := quotMkApp_data (u := u) (i := 4)
      (j := 3) (k := 2)
      (ρ := cons w (cons b (cons a (cons R (cons Aset ρ)))))
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hAset hR ha
    obtain ⟨hrok, hrval, hrint⟩ := quotMkApp_data (u := u) (i := 4)
      (j := 3) (k := 1)
      (ρ := cons w (cons b (cons a (cons R (cons Aset ρ)))))
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hAset hR hb
    exact hgr _ _ _ _ ⟨hTok, hTval⟩ ⟨hlok, hlval⟩ ⟨hrok, hrval⟩
      (by rw [hTint]; exact quotSet_mem_univ hAset)
      (by rw [hTint, hlint]; exact quotClass_mem ha)
      (by rw [hTint, hrint]; exact quotClass_mem hb)
  have h5 : ∀ Aset R a b : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace V u Aset → a ∈ˢ Aset → b ∈ˢ Aset →
      WellDenotedV V (cons b (cons a (cons R (cons Aset ρ))))
          (.pi 0 0 (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
            (.app (.app (.app E (quotApp u 4 3)) (quotMkApp u 4 3 2))
              (quotMkApp u 4 3 1))) ∧
        interp V (cons b (cons a (cons R (cons Aset ρ))))
          (.pi 0 0 (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
            (.app (.app (.app E (quotApp u 4 3)) (quotMkApp u 4 3 2))
              (quotMkApp u 4 3 1))) ∈ˢ (univZero : V) := by
    intro Aset R a b hAset hR ha hb
    obtain ⟨hrok, hrval, -⟩ := relApp_data (u := u) (i := 2) (j := 1)
      (k := 0) (ρ := cons b (cons a (cons R (cons Aset ρ))))
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hR ha hb
    exact WellDenotedV_pi_zero ⟨hrok, hrval⟩
      (fun w _ => (hin Aset R a b w hAset hR ha hb).1)
      (fun w _ => (hin Aset R a b w hAset hR ha hb).2)
  have h4 : ∀ Aset R a : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace V u Aset → a ∈ˢ Aset →
      WellDenotedV V (cons a (cons R (cons Aset ρ)))
          (.pi 0 0 (.bvar 2)
            (.pi 0 0 (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
              (.app (.app (.app E (quotApp u 4 3))
                (quotMkApp u 4 3 2)) (quotMkApp u 4 3 1)))) ∧
        interp V (cons a (cons R (cons Aset ρ)))
          (.pi 0 0 (.bvar 2)
            (.pi 0 0 (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
              (.app (.app (.app E (quotApp u 4 3))
                (quotMkApp u 4 3 2)) (quotMkApp u 4 3 1))))
          ∈ˢ (univZero : V) := by
    intro Aset R a hAset hR ha
    have hdom : interp V (cons a (cons R (cons Aset ρ)))
        (AnnotTerm.bvar 2) = Aset := by simp [interp_bvar, cons]
    exact WellDenotedV_pi_zero (Aa := .bvar 2) ⟨trivial, trivial⟩
      (fun b hb => (h5 Aset R a b hAset hR ha (by rwa [hdom] at hb)).1)
      (fun b hb => (h5 Aset R a b hAset hR ha (by rwa [hdom] at hb)).2)
  have h3 : ∀ Aset R : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace V u Aset →
      WellDenotedV V (cons R (cons Aset ρ))
          (.pi 0 0 (.bvar 1)
            (.pi 0 0 (.bvar 2)
              (.pi 0 0 (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
                (.app (.app (.app E (quotApp u 4 3))
                  (quotMkApp u 4 3 2)) (quotMkApp u 4 3 1))))) ∧
        interp V (cons R (cons Aset ρ))
          (.pi 0 0 (.bvar 1)
            (.pi 0 0 (.bvar 2)
              (.pi 0 0 (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
                (.app (.app (.app E (quotApp u 4 3))
                  (quotMkApp u 4 3 2)) (quotMkApp u 4 3 1)))))
          ∈ˢ (univZero : V) := by
    intro Aset R hAset hR
    have hdom : interp V (cons R (cons Aset ρ)) (AnnotTerm.bvar 1)
        = Aset := by simp [interp_bvar, cons]
    exact WellDenotedV_pi_zero (Aa := .bvar 1) ⟨trivial, trivial⟩
      (fun a ha => (h4 Aset R a hAset hR (by rwa [hdom] at ha)).1)
      (fun a ha => (h4 Aset R a hAset hR (by rwa [hdom] at ha)).2)
  have h2 : ∀ Aset : V, Aset ∈ˢ (univ u : V) →
      WellDenotedV V (cons Aset ρ)
          (.pi 0 0 quotRelTy
            (.pi 0 0 (.bvar 1)
              (.pi 0 0 (.bvar 2)
                (.pi 0 0 (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
                  (.app (.app (.app E (quotApp u 4 3))
                    (quotMkApp u 4 3 2)) (quotMkApp u 4 3 1)))))) ∧
        interp V (cons Aset ρ)
          (.pi 0 0 quotRelTy
            (.pi 0 0 (.bvar 1)
              (.pi 0 0 (.bvar 2)
                (.pi 0 0 (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
                  (.app (.app (.app E (quotApp u 4 3))
                    (quotMkApp u 4 3 2)) (quotMkApp u 4 3 1))))))
          ∈ˢ (univZero : V) := by
    intro Aset hAset
    exact WellDenotedV_pi_zero (Aa := quotRelTy) (quotRelTy_wellDenotedV _)
      (fun R hR => (h3 Aset R hAset
        (by rwa [quotRelTy_interp u] at hR)).1)
      (fun R hR => (h3 Aset R hAset
        (by rwa [quotRelTy_interp u] at hR)).2)
  rw [quotSoundTy]
  exact (WellDenotedV_pi_zero (Aa := .sort u) ⟨trivial, trivial⟩
    (fun Aset hAset => (h2 Aset (by rwa [interp_sort] at hAset)).1)
    (fun Aset hAset => (h2 Aset (by rwa [interp_sort] at hAset)).2)).1

/-- **`Quot.sound` inhabits its type's reading.**  Five
`pt_mem_piR_zero` steps; the innermost witness is the quotient's own
soundness (`SetTheory.quotSound`), read through `EqLaw`'s value
half. -/
theorem quotSoundTy_mem {E : AnnotTerm} {u : Nat} (ρ : Nat → V)
    (hval : ∀ (ρ' : Nat → V) (T a b : V), T ∈ˢ (univ u : V) →
      a ∈ˢ T → b ∈ˢ T →
      app (app (app (interp V ρ' E) T) a) b = eqv a b) :
    (pt : V) ∈ˢ interp V ρ (quotSoundTy E u) := by
  rw [quotSoundTy, interp_pi]
  refine pt_mem_piR_zero fun Aset hAset => ⟨pt, ?_⟩
  rw [interp_sort] at hAset
  rw [interp_pi]
  refine pt_mem_piR_zero fun R hR => ⟨pt, ?_⟩
  rw [quotRelTy_interp u] at hR
  rw [interp_pi]
  refine pt_mem_piR_zero fun a ha => ⟨pt, ?_⟩
  rw [show interp V (cons R (cons Aset ρ)) (AnnotTerm.bvar 1) = Aset
    from by simp [interp_bvar, cons]] at ha
  rw [interp_pi]
  refine pt_mem_piR_zero fun b hb => ⟨pt, ?_⟩
  rw [show interp V (cons a (cons R (cons Aset ρ))) (AnnotTerm.bvar 2)
    = Aset from by simp [interp_bvar, cons]] at hb
  rw [interp_pi]
  refine pt_mem_piR_zero fun w hw => ⟨pt, ?_⟩
  obtain ⟨-, -, hrint⟩ := relApp_data (u := u) (i := 2) (j := 1) (k := 0)
    (ρ := cons b (cons a (cons R (cons Aset ρ))))
    (by simp [cons]) (by simp [cons]) (by simp [cons]) hR ha hb
  rw [hrint] at hw
  obtain ⟨-, -, hTint⟩ := quotApp_data (u := u) (i := 4) (j := 3)
    (ρ := cons w (cons b (cons a (cons R (cons Aset ρ)))))
    (by simp [cons]) (by simp [cons]) hAset hR
  obtain ⟨-, -, hlint⟩ := quotMkApp_data (u := u) (i := 4) (j := 3)
    (k := 2) (ρ := cons w (cons b (cons a (cons R (cons Aset ρ)))))
    (by simp [cons]) (by simp [cons]) (by simp [cons]) hAset hR ha
  obtain ⟨-, -, hrint'⟩ := quotMkApp_data (u := u) (i := 4) (j := 3)
    (k := 1) (ρ := cons w (cons b (cons a (cons R (cons Aset ρ)))))
    (by simp [cons]) (by simp [cons]) (by simp [cons]) hAset hR hb
  rw [interp_app, interp_app, interp_app, hTint, hlint, hrint',
    hval _ _ _ _ (quotSet_mem_univ hAset) (quotClass_mem ha)
      (quotClass_mem hb),
    quotSound (u := u) ha hb hw]
  exact pt_mem_eqv_self _

/-- **`Quot.sound`, installed at the P tier** — the basis blocks' one
stored axiom, and the one place the `reduce_ops` disjunct's second
branch is taken. -/
theorem extendQuotSound (mp : EnvModelM V μ env)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hE : env.find? eqName = some eqA)
    (hfresh : env.find? quotSoundA.name = none)
    (hwf : EnvWF ⟨quotSoundA :: env.consts⟩) :
    Nonempty (EnvModelM V μ ⟨quotSoundA :: env.consts⟩) := by
  have hty := fun ψ =>
    denoteMeta_quotSoundA_type (m := mp.base2)
      (A := fun ψ => AnnotTerm.const .quotSound [ψ uN]) ψ hQ hM hE
  refine nonempty_of_exists (declStep_preserves_of_basis_cons mp
    (A := fun ψ => AnnotTerm.const .quotSound [ψ uN]) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h)
    (Or.inl (by decide)) (Or.inr (by decide))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT quotSoundA.name ψ
          = some (Term.const .quotSound [ψ uN]) from rfl] at hp
        rw [← Option.some.inj hp]
        rfl)
      (fun _ h => nomatch h) (fun _ _ _ _ h => nomatch h))
    (fun _ _ => rfl) ?_
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_)
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact quotSoundTy_wellDenotedV ρ (mp.eq_law hE ψ).2
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [interp_const]
    show (pt : V) ∈ˢ _
    exact quotSoundTy_mem ρ (mp.eq_law hE ψ).1

/-! ## `Quot.lift`

The block's last constant, and the only one whose type reading is not
`Prop`-valued: its six binders carry `.ifAllZero [v]`, so their bit is
`0` exactly when the target sort is — which is precisely the condition
`quotLiftV`'s own two regimes are separated by (`quotLiftV_app_any`,
ENDGAME G §4).  The invariance premise is `Prop`-valued throughout and
concludes at the `Eq` former read **at `v`**, so the bridge is
`EqLaw` at the substituted assignment. -/

/-- A `.pi` at a pin's bit: graded when the domain and body are, with
the squash clause conditional on the bit. -/
theorem WellDenotedV_pi_bit {ρ : Nat → V} {b : Nat} {Aa B : AnnotTerm}
    (hA : WellDenotedV V ρ Aa)
    (hB : ∀ x, x ∈ˢ interp V ρ Aa → WellDenotedV V (cons x ρ) B)
    (hz : b = 0 → ∀ x, x ∈ˢ interp V ρ Aa →
      interp V (cons x ρ) B ∈ˢ (univZero : V)) :
    WellDenotedV V ρ (.pi 0 b Aa B) :=
  ⟨⟨hA.1, fun x hx => (hB x hx).1⟩,
    ⟨hA.2, fun x hx => (hB x hx).2, hz⟩⟩

/-- **A `λ` at a pin's bit, graded and placed at once** — the combined
step every basis tower's walk takes: the fibre named once serves both
`WellDenoted`'s existential and `lamR_mem`'s hypothesis. -/
theorem WellDenotedV_lam_mem {ρ : Nat → V} {b : Nat} {Aa bd : AnnotTerm}
    {F : V → V} (hA : WellDenotedV V ρ Aa)
    (hb : ∀ x, x ∈ˢ interp V ρ Aa → WellDenotedV V (cons x ρ) bd ∧
      interp V (cons x ρ) bd ∈ˢ F x)
    (hz : b = 0 → ∀ x, x ∈ˢ interp V ρ Aa → F x ∈ˢ (univZero : V)) :
    WellDenotedV V ρ (.lam b Aa bd) ∧
      interp V ρ (.lam b Aa bd) ∈ˢ piR b (interp V ρ Aa) F := by
  refine ⟨⟨⟨hA.1, fun x hx => (hb x hx).1.1, F,
      fun x hx => (hb x hx).2, hz⟩,
    ⟨hA.2, fun x hx => (hb x hx).1.2⟩⟩, ?_⟩
  rw [interp_lam]
  exact lamR_mem fun x hx => (hb x hx).2

/-- `Quot.lift`'s invariance premise, read. -/
def quotLiftInvTy (E : AnnotTerm) : AnnotTerm :=
  .pi 0 0 (.bvar 3)
    (.pi 0 0 (.bvar 4)
      (.pi 0 0 (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
        (.app (.app (.app E (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
          (.app (.bvar 3) (.bvar 1)))))

/-- `Quot.lift`'s type reading, named. -/
def quotLiftTy (E : AnnotTerm) (b u v : Nat) : AnnotTerm :=
  .pi 0 b (.sort u)
    (.pi 0 b quotRelTy
      (.pi 0 b (.sort v)
        (.pi 0 b (.pi 0 b (.bvar 2) (.bvar 1))
          (.pi 0 b (quotLiftInvTy E)
            (.pi 0 b (quotApp u 4 3) (.bvar 3))))))

/-- **The invariance premise's reading is `quotInvSpace`, and it is
graded** — the `Eq` bridge's two halves, at the three-binder
`Prop`-valued telescope `Interp/Value.lean` states the law at. -/
theorem quotLiftInvTy_data {E : AnnotTerm} {u v : Nat} {Aset R B f : V}
    (ρ : Nat → V)
    (hval : ∀ (ρ' : Nat → V) (T x y : V), T ∈ˢ (univ v : V) →
      x ∈ˢ T → y ∈ˢ T →
      app (app (app (interp V ρ' E) T) x) y = eqv x y)
    (hgr : ∀ (ρ' : Nat → V) (Aa la ra : AnnotTerm),
      WellDenotedV V ρ' Aa → WellDenotedV V ρ' la → WellDenotedV V ρ' ra →
      interp V ρ' Aa ∈ˢ (univ v : V) →
      interp V ρ' la ∈ˢ interp V ρ' Aa →
      interp V ρ' ra ∈ˢ interp V ρ' Aa →
      WellDenotedV V ρ' (.app (.app (.app E Aa) la) ra) ∧
        interp V ρ' (.app (.app (.app E Aa) la) ra)
          ∈ˢ (univZero : V))
    (hR : R ∈ˢ relSpace V u Aset) (hB : B ∈ˢ (univ v : V))
    {bf : Nat} (hf : f ∈ˢ piR bf Aset fun _ => B)
    (hbf : bf = 0 → B ∈ˢ (univZero : V)) :
    interp V (cons f (cons B (cons R (cons Aset ρ))))
        (quotLiftInvTy E) = quotInvSpace V Aset R f ∧
      WellDenotedV V (cons f (cons B (cons R (cons Aset ρ))))
        (quotLiftInvTy E) := by
  have hfm : ∀ a : V, a ∈ˢ Aset → app f a ∈ˢ B := fun a ha =>
    app_mem_piR hf ha fun h _ _ => hbf h
  have hd1 : interp V (cons f (cons B (cons R (cons Aset ρ)))) (AnnotTerm.bvar 3) = Aset := by
    simp [interp_bvar, cons]
  have hd2 : ∀ a : V, interp V (cons a (cons f (cons B (cons R (cons Aset ρ))))) (AnnotTerm.bvar 4) = Aset := by
    intro a; simp [interp_bvar, cons]
  have hbody : ∀ a b : V, a ∈ˢ Aset → b ∈ˢ Aset → ∀ w : V,
      interp V (cons w (cons b (cons a (cons f (cons B (cons R (cons Aset ρ)))))))
          (.app (.app (.app E (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
            (.app (.bvar 3) (.bvar 1)))
        = eqv (app f a) (app f b) ∧
      WellDenotedV V (cons w (cons b (cons a (cons f (cons B (cons R (cons Aset ρ)))))))
          (.app (.app (.app E (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
            (.app (.bvar 3) (.bvar 1))) ∧
      interp V (cons w (cons b (cons a (cons f (cons B (cons R (cons Aset ρ)))))))
          (.app (.app (.app E (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
            (.app (.bvar 3) (.bvar 1))) ∈ˢ (univZero : V) := by
    intro a b ha hb w
    have hB' : interp V (cons w (cons b (cons a (cons f (cons B (cons R (cons Aset ρ))))))) (AnnotTerm.bvar 4)
        = B := by simp [interp_bvar, cons]
    have hfa : interp V (cons w (cons b (cons a (cons f (cons B (cons R (cons Aset ρ)))))))
        (.app (.bvar 3) (.bvar 2)) = app f a := by
      simp [interp_app, interp_bvar, cons]
    have hfb : interp V (cons w (cons b (cons a (cons f (cons B (cons R (cons Aset ρ)))))))
        (.app (.bvar 3) (.bvar 1)) = app f b := by
      simp [interp_app, interp_bvar, cons]
    have hfslot : interp V (cons w (cons b (cons a
        (cons f (cons B (cons R (cons Aset ρ))))))) (AnnotTerm.bvar 3)
        = f := by simp [interp_bvar, cons]
    have haslot : interp V (cons w (cons b (cons a
        (cons f (cons B (cons R (cons Aset ρ))))))) (AnnotTerm.bvar 2)
        = a := by simp [interp_bvar, cons]
    have hbslot : interp V (cons w (cons b (cons a
        (cons f (cons B (cons R (cons Aset ρ))))))) (AnnotTerm.bvar 1)
        = b := by simp [interp_bvar, cons]
    have hokfa : WellDenoted V (cons w (cons b (cons a
        (cons f (cons B (cons R (cons Aset ρ)))))))
        (.app (.bvar 3) (.bvar 2)) := by
      rw [WellDenoted_app]
      exact ⟨trivial, trivial, bf, Aset, fun _ => B,
        by rw [hfslot]; exact hf, by rw [haslot]; exact ha,
        fun h _ _ => hbf h⟩
    have hokfb : WellDenoted V (cons w (cons b (cons a
        (cons f (cons B (cons R (cons Aset ρ)))))))
        (.app (.bvar 3) (.bvar 1)) := by
      rw [WellDenoted_app]
      exact ⟨trivial, trivial, bf, Aset, fun _ => B,
        by rw [hfslot]; exact hf, by rw [hbslot]; exact hb,
        fun h _ _ => hbf h⟩
    have hspine := hgr _ (.bvar 4) (.app (.bvar 3) (.bvar 2))
      (.app (.bvar 3) (.bvar 1)) ⟨trivial, trivial⟩
      ⟨hokfa, ⟨trivial, trivial⟩⟩
      ⟨hokfb, ⟨trivial, trivial⟩⟩
      (by rw [hB']; exact hB)
      (by rw [hB', hfa]; exact hfm a ha)
      (by rw [hB', hfb]; exact hfm b hb)
    refine ⟨?_, hspine.1, hspine.2⟩
    rw [interp_app, interp_app, interp_app, hB', hfa, hfb,
      hval _ _ _ _ hB (hfm a ha) (hfm b hb)]
  constructor
  · rw [quotLiftInvTy, interp_pi, quotInvSpace, hd1]
    refine piR_congr fun a ha => ?_
    rw [interp_pi, hd2 a]
    refine piR_congr fun b hb => ?_
    obtain ⟨-, -, hrint⟩ := relApp_data (u := u) (i := 4) (j := 1)
      (k := 0) (ρ := cons b (cons a (cons f (cons B (cons R (cons Aset ρ))))))
      (by simp [cons]) (by simp [cons]) (by simp [cons])
      hR ha hb
    rw [interp_pi, hrint]
    exact piR_congr fun w _ => (hbody a b ha hb w).1
  · rw [quotLiftInvTy]
    refine (WellDenotedV_pi_zero (Aa := .bvar 3) ⟨trivial, trivial⟩ ?_ ?_).1
    all_goals (
      intro a ha
      rw [hd1] at ha
      have hstep : ∀ b : V, b ∈ˢ Aset →
          WellDenotedV V (cons b (cons a (cons f (cons B (cons R (cons Aset ρ))))))
              (.pi 0 0 (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
                (.app (.app (.app E (.bvar 4))
                  (.app (.bvar 3) (.bvar 2)))
                  (.app (.bvar 3) (.bvar 1)))) ∧
            interp V (cons b (cons a (cons f (cons B (cons R (cons Aset ρ))))))
              (.pi 0 0 (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
                (.app (.app (.app E (.bvar 4))
                  (.app (.bvar 3) (.bvar 2)))
                  (.app (.bvar 3) (.bvar 1)))) ∈ˢ (univZero : V) := by
        intro b hb
        obtain ⟨hrok, hrval, -⟩ := relApp_data (u := u) (i := 4)
          (j := 1) (k := 0) (ρ := cons b (cons a (cons f (cons B (cons R (cons Aset ρ))))))
          (by simp [cons]) (by simp [cons])
          (by simp [cons]) hR ha hb
        exact WellDenotedV_pi_zero ⟨hrok, hrval⟩
          (fun w _ => (hbody a b ha hb w).2.1)
          (fun w _ => (hbody a b ha hb w).2.2)
      have hlev : WellDenotedV V (cons a (cons f (cons B (cons R (cons Aset ρ)))))
            (.pi 0 0 (.bvar 4)
              (.pi 0 0 (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
                (.app (.app (.app E (.bvar 4))
                  (.app (.bvar 3) (.bvar 2)))
                  (.app (.bvar 3) (.bvar 1))))) ∧
          interp V (cons a (cons f (cons B (cons R (cons Aset ρ)))))
            (.pi 0 0 (.bvar 4)
              (.pi 0 0 (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
                (.app (.app (.app E (.bvar 4))
                  (.app (.bvar 3) (.bvar 2)))
                  (.app (.bvar 3) (.bvar 1)))))
            ∈ˢ (univZero : V) :=
        WellDenotedV_pi_zero (Aa := .bvar 4) ⟨trivial, trivial⟩
          (fun b hb => (hstep b (by rwa [hd2 a] at hb)).1)
          (fun b hb => (hstep b (by rwa [hd2 a] at hb)).2))
    case _ => exact hlev.1
    case _ => exact hlev.2

/-- **`Quot.lift`'s type reading is graded.**  Six
`WellDenotedV_pi_bit` steps; every squash clause is discharged by the
product below it being a `piR 0`, except the innermost, where the
target sort itself is `0`. -/
theorem quotLiftTy_wellDenotedV {E : AnnotTerm} {b u v : Nat} (hz : b = 0 ↔ v = 0)
    (hval : ∀ (ρ' : Nat → V) (T x y : V), T ∈ˢ (univ v : V) →
      x ∈ˢ T → y ∈ˢ T →
      app (app (app (interp V ρ' E) T) x) y = eqv x y)
    (hgr : ∀ (ρ' : Nat → V) (Aa la ra : AnnotTerm),
      WellDenotedV V ρ' Aa → WellDenotedV V ρ' la → WellDenotedV V ρ' ra →
      interp V ρ' Aa ∈ˢ (univ v : V) →
      interp V ρ' la ∈ˢ interp V ρ' Aa →
      interp V ρ' ra ∈ˢ interp V ρ' Aa →
      WellDenotedV V ρ' (.app (.app (.app E Aa) la) ra) ∧
        interp V ρ' (.app (.app (.app E Aa) la) ra)
          ∈ˢ (univZero : V))
    (ρ : Nat → V) :
    WellDenotedV V ρ (quotLiftTy E b u v) := by
  have h6 : ∀ Aset R B f h : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace V u Aset → B ∈ˢ (univ v : V) →
      WellDenotedV V (cons h (cons f (cons B (cons R (cons Aset ρ)))))
        (.pi 0 b (quotApp u 4 3) (.bvar 3)) := by
    intro Aset R B f h hAset hR hB
    obtain ⟨hqok, hqval, -⟩ := quotApp_data (u := u) (i := 4) (j := 3)
      (ρ := cons h (cons f (cons B (cons R (cons Aset ρ)))))
      (by simp [cons]) (by simp [cons]) hAset hR
    refine WellDenotedV_pi_bit ⟨hqok, hqval⟩ (fun _ _ => ⟨trivial, trivial⟩)
      (fun hb0 q _ => ?_)
    rw [show interp V (cons q (cons h (cons f (cons B
        (cons R (cons Aset ρ)))))) (AnnotTerm.bvar 3) = B
      from by simp [interp_bvar, cons], ← univ_zero, ← hz.mp hb0]
    exact hB
  have h5 : ∀ Aset R B f : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace V u Aset → B ∈ˢ (univ v : V) →
      f ∈ˢ piR b Aset (fun _ => B) →
      WellDenotedV V (cons f (cons B (cons R (cons Aset ρ))))
        (.pi 0 b (quotLiftInvTy E)
          (.pi 0 b (quotApp u 4 3) (.bvar 3))) := by
    intro Aset R B f hAset hR hB hf
    obtain ⟨-, hinv⟩ := quotLiftInvTy_data (u := u) ρ hval hgr hR hB
      hf (fun hb0 => by rw [← univ_zero, ← hz.mp hb0]; exact hB)
    refine WellDenotedV_pi_bit hinv
      (fun h _ => h6 Aset R B f h hAset hR hB) (fun hb0 h _ => ?_)
    rw [interp_pi, hb0]
    exact piR_zero_mem_univZero
  have h4 : ∀ Aset R B : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace V u Aset → B ∈ˢ (univ v : V) →
      WellDenotedV V (cons B (cons R (cons Aset ρ)))
        (.pi 0 b (.pi 0 b (.bvar 2) (.bvar 1))
          (.pi 0 b (quotLiftInvTy E)
            (.pi 0 b (quotApp u 4 3) (.bvar 3)))) := by
    intro Aset R B hAset hR hB
    have hdom : interp V (cons B (cons R (cons Aset ρ)))
        (AnnotTerm.pi 0 b (.bvar 2) (.bvar 1))
        = piR b Aset (fun _ => B) := by
      rw [interp_pi]
      simp only [interp_bvar, cons]
    refine WellDenotedV_pi_bit ?_ (fun f hf => ?_) (fun hb0 f _ => ?_)
    · refine WellDenotedV_pi_bit (Aa := .bvar 2) ⟨trivial, trivial⟩
        (fun _ _ => ⟨trivial, trivial⟩) (fun hb0 a _ => ?_)
      rw [show interp V (cons a (cons B (cons R (cons Aset ρ))))
          (AnnotTerm.bvar 1) = B from by simp [interp_bvar, cons],
        ← univ_zero, ← hz.mp hb0]
      exact hB
    · exact h5 Aset R B f hAset hR hB (by rwa [hdom] at hf)
    · rw [interp_pi, hb0]
      exact piR_zero_mem_univZero
  have h3 : ∀ Aset R : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace V u Aset →
      WellDenotedV V (cons R (cons Aset ρ))
        (.pi 0 b (.sort v)
          (.pi 0 b (.pi 0 b (.bvar 2) (.bvar 1))
            (.pi 0 b (quotLiftInvTy E)
              (.pi 0 b (quotApp u 4 3) (.bvar 3))))) := by
    intro Aset R hAset hR
    refine WellDenotedV_pi_bit (Aa := .sort v) ⟨trivial, trivial⟩
      (fun B hB => h4 Aset R B hAset hR (by rwa [interp_sort] at hB))
      (fun hb0 B _ => ?_)
    rw [interp_pi, hb0]
    exact piR_zero_mem_univZero
  have h2 : ∀ Aset : V, Aset ∈ˢ (univ u : V) →
      WellDenotedV V (cons Aset ρ)
        (.pi 0 b quotRelTy
          (.pi 0 b (.sort v)
            (.pi 0 b (.pi 0 b (.bvar 2) (.bvar 1))
              (.pi 0 b (quotLiftInvTy E)
                (.pi 0 b (quotApp u 4 3) (.bvar 3)))))) := by
    intro Aset hAset
    refine WellDenotedV_pi_bit (Aa := quotRelTy) (quotRelTy_wellDenotedV _)
      (fun R hR => h3 Aset R hAset (by rwa [quotRelTy_interp u] at hR))
      (fun hb0 R _ => ?_)
    rw [interp_pi, hb0]
    exact piR_zero_mem_univZero
  rw [quotLiftTy]
  refine WellDenotedV_pi_bit (Aa := .sort u) ⟨trivial, trivial⟩
    (fun Aset hAset => h2 Aset (by rwa [interp_sort] at hAset))
    (fun hb0 Aset _ => ?_)
  rw [interp_pi, hb0]
  exact piR_zero_mem_univZero

/-- **`Quot.lift` inhabits its type's reading.**  Six
`lamR_mem_zero_agree` steps against `quotLiftV`'s own tower, with
`quotLiftR_mem` at the bottom; the bit/level conversion is `hz` at
every level, which is the same fact that makes `quotLiftV_app_any`
premise-free. -/
theorem quotLiftTy_mem {E : AnnotTerm} {b u v : Nat} (hz : b = 0 ↔ v = 0)
    (hval : ∀ (ρ' : Nat → V) (T x y : V), T ∈ˢ (univ v : V) →
      x ∈ˢ T → y ∈ˢ T →
      app (app (app (interp V ρ' E) T) x) y = eqv x y)
    (hgr : ∀ (ρ' : Nat → V) (Aa la ra : AnnotTerm),
      WellDenotedV V ρ' Aa → WellDenotedV V ρ' la → WellDenotedV V ρ' ra →
      interp V ρ' Aa ∈ˢ (univ v : V) →
      interp V ρ' la ∈ˢ interp V ρ' Aa →
      interp V ρ' ra ∈ˢ interp V ρ' Aa →
      WellDenotedV V ρ' (.app (.app (.app E Aa) la) ra) ∧
        interp V ρ' (.app (.app (.app E Aa) la) ra)
          ∈ˢ (univZero : V))
    (ρ : Nat → V) :
    quotLiftV V u v ∈ˢ interp V ρ (quotLiftTy E b u v) := by
  have hzv : v = 0 ↔ b = 0 := hz.symm
  rw [quotLiftTy, quotLiftV, interp_pi, interp_sort]
  refine lamR_mem_zero_agree hzv fun Aset hAset => ?_
  rw [interp_pi, quotRelTy_interp u]
  refine lamR_mem_zero_agree hzv fun R hR => ?_
  rw [interp_pi, interp_sort]
  refine lamR_mem_zero_agree hzv fun B hB => ?_
  have hdom : interp V (cons B (cons R (cons Aset ρ)))
      (AnnotTerm.pi 0 b (.bvar 2) (.bvar 1))
      = piR v Aset (fun _ => B) := by
    rw [interp_pi]
    simp only [interp_bvar, cons]
    exact piR_zero_agree hz fun _ _ => rfl
  rw [interp_pi, hdom]
  refine lamR_mem_zero_agree hzv fun f hf => ?_
  have hfb : f ∈ˢ piR b Aset fun _ => B := by
    rwa [piR_zero_agree hz (fun _ _ => rfl) (B := fun _ => B)]
  obtain ⟨hinvint, -⟩ := quotLiftInvTy_data (u := u) ρ hval hgr hR hB
    hfb (fun hb0 => by rw [← univ_zero, ← hz.mp hb0]; exact hB)
  rw [interp_pi, hinvint]
  refine lamR_mem_zero_agree hzv fun h hh => ?_
  obtain ⟨-, -, hqint⟩ := quotApp_data (u := u) (i := 4) (j := 3)
    (ρ := cons h (cons f (cons B (cons R (cons Aset ρ)))))
    (by simp [cons]) (by simp [cons]) hAset hR
  rw [interp_pi, hqint]
  have hfib : ∀ q : V, q ∈ˢ quotSet u Aset R →
      interp V (cons q (cons h (cons f (cons B
        (cons R (cons Aset ρ)))))) (AnnotTerm.bvar 3) = B := by
    intro q _; simp [interp_bvar, cons]
  rw [piR_congr hfib,
    show (piR b (quotSet u Aset R) fun _ => B)
      = piR v (quotSet u Aset R) (fun _ => B)
      from piR_zero_agree hz fun _ _ => rfl]
  exact quotLiftR_mem V hf fun hv0 => by
    rw [← univ_zero, ← hv0]; exact hB

/-! ### The substitution-peeling kit

`TeleFitPA` peels by `B.inst a` at cut `0`, so after `k` peels a
domain carries a *chain* of instantiations at cuts `k-1, …, 0`.
`interp_inst0` turns the outermost into a `cons`; these four turn the
rest into `cons`es too, so a `k`-deep telescope domain's reading is
read at the `k`-fold `cons` environment — which is the environment
every space lemma above is stated at.  (`BasisBlocksP.lean`'s
`interp_liftN_succ_inst` is the special case where the domain is a
*lifted* earlier argument; this is the general shape.) -/

theorem interp_inst_cons1 (e a : AnnotTerm) (x1 : V) (ρ : Nat → V) :
    interp V (cons x1 ρ) (e.inst a 1)
      = interp V (cons x1 (cons (interp V ρ a) ρ)) e := by
  have hsh : shiftE 1 0 (cons x1 ρ) = ρ := by
    funext j; simp [shiftE, cons]
  rw [interp_inst, hsh]
  congr 1
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl
  | (_ + 2) => rfl

theorem interp_inst_cons2 (e a : AnnotTerm) (x1 x2 : V) (ρ : Nat → V) :
    interp V (cons x2 (cons x1 ρ)) (e.inst a 2)
      = interp V (cons x2 (cons x1 (cons (interp V ρ a) ρ))) e := by
  have hsh : shiftE 2 0 (cons x2 (cons x1 ρ)) = ρ := by
    funext j; simp [shiftE, cons]
  rw [interp_inst, hsh]
  congr 1
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | (_ + 3) => rfl

theorem interp_inst_cons3 (e a : AnnotTerm) (x1 x2 x3 : V) (ρ : Nat → V) :
    interp V (cons x3 (cons x2 (cons x1 ρ))) (e.inst a 3)
      = interp V (cons x3 (cons x2 (cons x1 (cons (interp V ρ a) ρ))))
          e := by
  have hsh : shiftE 3 0 (cons x3 (cons x2 (cons x1 ρ))) = ρ := by
    funext j; simp [shiftE, cons]
  rw [interp_inst, hsh]
  congr 1
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | (_ + 4) => rfl

theorem interp_inst_cons4 (e a : AnnotTerm) (x1 x2 x3 x4 : V)
    (ρ : Nat → V) :
    interp V (cons x4 (cons x3 (cons x2 (cons x1 ρ)))) (e.inst a 4)
      = interp V (cons x4 (cons x3 (cons x2 (cons x1
          (cons (interp V ρ a) ρ))))) e := by
  have hsh : shiftE 4 0 (cons x4 (cons x3 (cons x2 (cons x1 ρ)))) = ρ := by
    funext j; simp [shiftE, cons]
  rw [interp_inst, hsh]
  congr 1
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | (_ + 5) => rfl

/-- Every stored leaf absorbs instantiation: `EnvS.cval_closed`
through `EnvModel.acval_erase` and `AnnotTerm.inst_eq_self`. -/
theorem acval_inst_eq_self (m : EnvModel V env) (n : Name)
    (ψ : Name → Nat) (a : AnnotTerm) (k : Nat) :
    (m.acval n ψ).inst a k = m.acval n ψ :=
  AnnotTerm.inst_eq_self _
    (Term.bvarsBelow.mono (Nat.zero_le k)
      (by rw [m.acval_erase]; exact m.cval_closed n ψ)) a

/-! ### `Quot.lift`'s type reading, and its rule -/

/-- **`Quot.lift`'s type reading.** -/
theorem denoteMeta_quotLiftA_type (ψ : Name → Nat)
    (hQ : env.find? quotName = some quotA)
    (hE : env.find? eqName = some eqA) :
    denoteMeta (acvalWith m.acval quotLiftA.name A)
        ⟨quotLiftA :: env.consts⟩ ψ 0 quotLiftA.toConstantVal.type
      = some (quotLiftTy
          (m.acval eqName (Level.substFn ψ [uN] [Level.param vN]))
          (pwBit ψ (.ifAllZero [vN])) (ψ uN) (ψ vN)) := by
  have hQc : ∀ d : Nat,
      denoteMeta (acvalWith m.acval quotLiftA.name A)
        ⟨quotLiftA :: env.consts⟩ ψ d (.const quotName [.param uN])
        = some (AnnotTerm.const .quot [ψ uN]) := fun d =>
    denoteMeta_quotLeaf (m := m) (A := A) ψ (by decide) hQ d
      (Level.param uN)
  have hEc : ∀ d : Nat,
      denoteMeta (acvalWith m.acval quotLiftA.name A)
        ⟨quotLiftA :: env.consts⟩ ψ d (.const eqName [.param vN])
        = some (m.acval eqName
            (Level.substFn ψ [uN] [Level.param vN])) := fun d =>
    denoteMeta_eqLeaf (m := m) (A := A) ψ (Level.param vN) (by decide)
      hE d
  rw [show quotLiftA.toConstantVal.type
      = Expr.forallE (.sort (.param uN))
          (Expr.forallE
            (Expr.forallE (.bvar 0)
              (Expr.forallE (.bvar 1) (.sort .zero)
                { pw := .never })
              { pw := .never })
            (Expr.forallE (.sort (.param vN))
              (Expr.forallE
                (Expr.forallE (.bvar 2)
                  (.bvar 1) { pw := .ifAllZero [vN] })
                (Expr.forallE
                  (Expr.forallE (.bvar 3)
                    (Expr.forallE (.bvar 4)
                      (Expr.forallE
                        (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
                        (.app (.app (.app (.const eqName [.param vN])
                          (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
                          (.app (.bvar 3) (.bvar 1)))
                        { pw := .ifAllZero [] })
                      { pw := .ifAllZero [] })
                    { pw := .ifAllZero [] })
                  (Expr.forallE
                    (.app (.app (.const quotName [.param uN]) (.bvar 4))
                      (.bvar 3))
                    (.bvar 3) { pw := .ifAllZero [vN] })
                  { pw := .ifAllZero [vN] })
                { pw := .ifAllZero [vN] })
              { pw := .ifAllZero [vN] })
            { pw := .ifAllZero [vN] })
          { pw := .ifAllZero [vN] } from rfl]
  simp [denoteMeta_forallE, denoteMeta_sort, denoteMeta_app, denoteMeta_fvar,
    Expr.instantiate1, quotRelTy, quotApp, quotLiftInvTy,
    quotLiftTy, pwBit_never, pwBit_ifAllZero_nil, hQc, hEc,
    Level.eval]

/-- `Quot.lift`'s rule's RHS reading. -/
def quotLiftRa (E : AnnotTerm) (b u v : Nat) : AnnotTerm :=
  .lam b (.sort u)
    (.lam b quotRelTy
      (.lam b (.sort v)
        (.lam b (.pi 0 b (.bvar 2) (.bvar 1))
          (.lam b (quotLiftInvTy E)
            (.lam b (.bvar 4) (.app (.bvar 2) (.bvar 0)))))))

/-- **`Quot.lift`'s rule's RHS reading.** -/
theorem denoteMeta_quotLift_rhs (ψ : Name → Nat)
    (hE : env.find? eqName = some eqA) :
    denoteMeta (acvalWith m.acval quotLiftA.name A)
        ⟨quotLiftA :: env.consts⟩ ψ 0 quotLiftRule.rhs
      = some (quotLiftRa
          (m.acval eqName (Level.substFn ψ [uN] [Level.param vN]))
          (pwBit ψ (.ifAllZero [vN])) (ψ uN) (ψ vN)) := by
  have hEc : ∀ d : Nat,
      denoteMeta (acvalWith m.acval quotLiftA.name A)
        ⟨quotLiftA :: env.consts⟩ ψ d (.const eqName [.param vN])
        = some (m.acval eqName
            (Level.substFn ψ [uN] [Level.param vN])) := fun d =>
    denoteMeta_eqLeaf (m := m) (A := A) ψ (Level.param vN) (by decide)
      hE d
  simp only [quotLiftRule]
  simp [denoteMeta_lam, denoteMeta_forallE, denoteMeta_sort, denoteMeta_app,
    denoteMeta_fvar, Expr.instantiate1, quotRelTy, quotLiftInvTy,
    quotLiftRa, pwBit_never, pwBit_ifAllZero_nil, hEc, Level.eval]

/-! ### The RHS tower's space, membership and grading -/

/-- The product the RHS tower inhabits. -/
noncomputable def quotLiftRaSpace (V : Type w) [SetTheory V]
    (b u v : Nat) : V :=
  piR b (univ u : V) fun Aset =>
    piR b (relSpace V u Aset) fun R =>
      piR b (univ v : V) fun B =>
        piR b (piR b Aset fun _ => B) fun f =>
          piR b (quotInvSpace V Aset R f) fun _ =>
            piR b Aset fun _ => B

/-- One application step, with the fibre named — the shape every
`RecRuleLaw` transport peels with. -/
theorem WellDenotedV_app_of {ρ : Nat → V} {f a : AnnotTerm} {w : Nat} {S : V}
    {F : V → V} (hf : WellDenotedV V ρ f) (ha : WellDenotedV V ρ a)
    (hfm : interp V ρ f ∈ˢ piR w S F) (ham : interp V ρ a ∈ˢ S)
    (hfib : w = 0 → ∀ x, x ∈ˢ S → F x ∈ˢ (univZero : V)) :
    WellDenotedV V ρ (.app f a) ∧
      interp V ρ (.app f a) ∈ˢ F (interp V ρ a) :=
  ⟨⟨by rw [WellDenoted_app]; exact ⟨hf.1, ha.1, w, S, F, hfm, ham, hfib⟩,
      ⟨hf.2, ha.2⟩⟩,
    by rw [interp_app]; exact app_mem_piR hfm ham hfib⟩

theorem quotLiftRa_mem {E : AnnotTerm} {b u v : Nat} (hz : b = 0 ↔ v = 0)
    (hval : ∀ (ρ' : Nat → V) (T x y : V), T ∈ˢ (univ v : V) →
      x ∈ˢ T → y ∈ˢ T →
      app (app (app (interp V ρ' E) T) x) y = eqv x y)
    (hgr : ∀ (ρ' : Nat → V) (Aa la ra : AnnotTerm),
      WellDenotedV V ρ' Aa → WellDenotedV V ρ' la → WellDenotedV V ρ' ra →
      interp V ρ' Aa ∈ˢ (univ v : V) →
      interp V ρ' la ∈ˢ interp V ρ' Aa →
      interp V ρ' ra ∈ˢ interp V ρ' Aa →
      WellDenotedV V ρ' (.app (.app (.app E Aa) la) ra) ∧
        interp V ρ' (.app (.app (.app E Aa) la) ra)
          ∈ˢ (univZero : V))
    (ρ : Nat → V) :
    interp V ρ (quotLiftRa E b u v) ∈ˢ quotLiftRaSpace V b u v := by
  rw [quotLiftRa, quotLiftRaSpace, interp_lam, interp_sort]
  refine lamR_mem fun Aset hAset => ?_
  rw [interp_lam, quotRelTy_interp u]
  refine lamR_mem fun R hR => ?_
  rw [interp_lam, interp_sort]
  refine lamR_mem fun B hB => ?_
  have hdom : interp V (cons B (cons R (cons Aset ρ)))
      (AnnotTerm.pi 0 b (.bvar 2) (.bvar 1)) = piR b Aset (fun _ => B) := by
    rw [interp_pi]; simp only [interp_bvar, cons]
  rw [interp_lam, hdom]
  refine lamR_mem fun f hf => ?_
  obtain ⟨hinvint, -⟩ := quotLiftInvTy_data (u := u) ρ hval hgr hR hB
    hf (fun hb0 => by rw [← univ_zero, ← hz.mp hb0]; exact hB)
  rw [interp_lam, hinvint]
  refine lamR_mem fun h hh => ?_
  rw [interp_lam,
    show interp V (cons h (cons f (cons B (cons R (cons Aset ρ)))))
      (AnnotTerm.bvar 4) = Aset from by simp [interp_bvar, cons]]
  refine lamR_mem fun a ha => ?_
  rw [show interp V (cons a (cons h (cons f (cons B
      (cons R (cons Aset ρ)))))) (.app (.bvar 2) (.bvar 0))
    = app f a from by simp [interp_app, interp_bvar, cons]]
  exact app_mem_piR hf ha fun hb0 _ _ => by
    rw [← univ_zero, ← hz.mp hb0]; exact hB

theorem quotLiftRa_wellDenotedV {E : AnnotTerm} {b u v : Nat} (hz : b = 0 ↔ v = 0)
    (hval : ∀ (ρ' : Nat → V) (T x y : V), T ∈ˢ (univ v : V) →
      x ∈ˢ T → y ∈ˢ T →
      app (app (app (interp V ρ' E) T) x) y = eqv x y)
    (hgr : ∀ (ρ' : Nat → V) (Aa la ra : AnnotTerm),
      WellDenotedV V ρ' Aa → WellDenotedV V ρ' la → WellDenotedV V ρ' ra →
      interp V ρ' Aa ∈ˢ (univ v : V) →
      interp V ρ' la ∈ˢ interp V ρ' Aa →
      interp V ρ' ra ∈ˢ interp V ρ' Aa →
      WellDenotedV V ρ' (.app (.app (.app E Aa) la) ra) ∧
        interp V ρ' (.app (.app (.app E Aa) la) ra)
          ∈ˢ (univZero : V))
    (ρ : Nat → V) :
    WellDenotedV V ρ (quotLiftRa E b u v) := by
  have hB0 : ∀ B : V, B ∈ˢ (univ v : V) → b = 0 →
      B ∈ˢ (univZero : V) := fun B hB hb0 => by
    rw [← univ_zero, ← hz.mp hb0]; exact hB
  have h6 : ∀ Aset R B f h : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace V u Aset → B ∈ˢ (univ v : V) →
      f ∈ˢ piR b Aset (fun _ => B) →
      WellDenotedV V (cons h (cons f (cons B (cons R (cons Aset ρ)))))
          (.lam b (.bvar 4) (.app (.bvar 2) (.bvar 0))) ∧
        interp V (cons h (cons f (cons B (cons R (cons Aset ρ)))))
          (.lam b (.bvar 4) (.app (.bvar 2) (.bvar 0)))
          ∈ˢ piR b Aset (fun _ => B) := by
    intro Aset R B f h hAset hR hB hf
    have hdom : interp V (cons h (cons f (cons B
        (cons R (cons Aset ρ))))) (AnnotTerm.bvar 4) = Aset := by
      simp [interp_bvar, cons]
    have hbody : ∀ a : V, a ∈ˢ Aset →
        interp V (cons a (cons h (cons f (cons B
          (cons R (cons Aset ρ)))))) (.app (.bvar 2) (.bvar 0))
          = app f a := by
      intro a _; simp [interp_app, interp_bvar, cons]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [WellDenoted_lam, hdom]
      refine ⟨trivial, fun a ha => ?_, fun _ => B, fun a ha => ?_,
        fun hb0 _ _ => hB0 B hB hb0⟩
      · rw [WellDenoted_app]
        refine ⟨trivial, trivial, b, Aset, fun _ => B, ?_, ?_,
          fun hb0 _ _ => hB0 B hB hb0⟩
        · rw [show interp V (cons a (cons h (cons f (cons B
              (cons R (cons Aset ρ)))))) (AnnotTerm.bvar 2) = f
            from by simp [interp_bvar, cons]]
          exact hf
        · rw [show interp V (cons a (cons h (cons f (cons B
              (cons R (cons Aset ρ)))))) (AnnotTerm.bvar 0) = a
            from by simp [interp_bvar, cons]]
          exact ha
      · rw [hbody a ha]
        exact app_mem_piR hf ha fun hb0 _ _ => hB0 B hB hb0
    · rw [AnnotValid_lam, hdom]
      exact ⟨trivial, fun _ _ => ⟨trivial, trivial⟩⟩
    · rw [interp_lam, hdom]
      refine lamR_mem fun a ha => ?_
      rw [hbody a ha]
      exact app_mem_piR hf ha fun hb0 _ _ => hB0 B hB hb0
  have h5 : ∀ Aset R B f : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace V u Aset → B ∈ˢ (univ v : V) →
      f ∈ˢ piR b Aset (fun _ => B) →
      WellDenotedV V (cons f (cons B (cons R (cons Aset ρ))))
          (.lam b (quotLiftInvTy E)
            (.lam b (.bvar 4) (.app (.bvar 2) (.bvar 0)))) ∧
        interp V (cons f (cons B (cons R (cons Aset ρ))))
          (.lam b (quotLiftInvTy E)
            (.lam b (.bvar 4) (.app (.bvar 2) (.bvar 0))))
          ∈ˢ piR b (quotInvSpace V Aset R f)
            (fun _ => piR b Aset (fun _ => B)) := by
    intro Aset R B f hAset hR hB hf
    obtain ⟨hinvint, hinvok⟩ := quotLiftInvTy_data (u := u) ρ hval hgr
      hR hB hf (fun hb0 => hB0 B hB hb0)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [WellDenoted_lam, hinvint]
      exact ⟨hinvok.1,
        fun h _ => (h6 Aset R B f h hAset hR hB hf).1.1,
        fun _ => piR b Aset (fun _ => B),
        fun h _ => (h6 Aset R B f h hAset hR hB hf).2,
        fun hb0 _ _ => by rw [hb0]; exact piR_zero_mem_univZero⟩
    · rw [AnnotValid_lam, hinvint]
      exact ⟨hinvok.2, fun h _ => (h6 Aset R B f h hAset hR hB hf).1.2⟩
    · rw [interp_lam, hinvint]
      exact lamR_mem fun h _ => (h6 Aset R B f h hAset hR hB hf).2
  have h4 : ∀ Aset R B : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace V u Aset → B ∈ˢ (univ v : V) →
      WellDenotedV V (cons B (cons R (cons Aset ρ)))
          (.lam b (.pi 0 b (.bvar 2) (.bvar 1))
            (.lam b (quotLiftInvTy E)
              (.lam b (.bvar 4) (.app (.bvar 2) (.bvar 0))))) ∧
        interp V (cons B (cons R (cons Aset ρ)))
          (.lam b (.pi 0 b (.bvar 2) (.bvar 1))
            (.lam b (quotLiftInvTy E)
              (.lam b (.bvar 4) (.app (.bvar 2) (.bvar 0)))))
          ∈ˢ piR b (piR b Aset (fun _ => B))
            (fun f => piR b (quotInvSpace V Aset R f)
              (fun _ => piR b Aset (fun _ => B))) := by
    intro Aset R B hAset hR hB
    have hdom : interp V (cons B (cons R (cons Aset ρ)))
        (AnnotTerm.pi 0 b (.bvar 2) (.bvar 1))
        = piR b Aset (fun _ => B) := by
      rw [interp_pi]; simp only [interp_bvar, cons]
    have hdok : WellDenotedV V (cons B (cons R (cons Aset ρ)))
        (AnnotTerm.pi 0 b (.bvar 2) (.bvar 1)) := by
      refine WellDenotedV_pi_bit (Aa := .bvar 2) ⟨trivial, trivial⟩
        (fun _ _ => ⟨trivial, trivial⟩) (fun hb0 a _ => ?_)
      rw [show interp V (cons a (cons B (cons R (cons Aset ρ))))
        (AnnotTerm.bvar 1) = B from by simp [interp_bvar, cons]]
      exact hB0 B hB hb0
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [WellDenoted_lam, hdom]
      exact ⟨hdok.1, fun f hf => (h5 Aset R B f hAset hR hB hf).1.1,
        fun f => piR b (quotInvSpace V Aset R f)
          (fun _ => piR b Aset (fun _ => B)),
        fun f hf => (h5 Aset R B f hAset hR hB hf).2,
        fun hb0 _ _ => by rw [hb0]; exact piR_zero_mem_univZero⟩
    · rw [AnnotValid_lam, hdom]
      exact ⟨hdok.2, fun f hf => (h5 Aset R B f hAset hR hB hf).1.2⟩
    · rw [interp_lam, hdom]
      exact lamR_mem fun f hf => (h5 Aset R B f hAset hR hB hf).2
  have h3 : ∀ Aset R : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace V u Aset →
      WellDenotedV V (cons R (cons Aset ρ))
          (.lam b (.sort v)
            (.lam b (.pi 0 b (.bvar 2) (.bvar 1))
              (.lam b (quotLiftInvTy E)
                (.lam b (.bvar 4) (.app (.bvar 2) (.bvar 0)))))) ∧
        interp V (cons R (cons Aset ρ))
          (.lam b (.sort v)
            (.lam b (.pi 0 b (.bvar 2) (.bvar 1))
              (.lam b (quotLiftInvTy E)
                (.lam b (.bvar 4) (.app (.bvar 2) (.bvar 0))))))
          ∈ˢ piR b (univ v : V) (fun B =>
            piR b (piR b Aset (fun _ => B))
              (fun f => piR b (quotInvSpace V Aset R f)
                (fun _ => piR b Aset (fun _ => B)))) := by
    intro Aset R hAset hR
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [WellDenoted_lam, interp_sort]
      exact ⟨trivial, fun B hB => (h4 Aset R B hAset hR hB).1.1,
        fun B => piR b (piR b Aset (fun _ => B))
          (fun f => piR b (quotInvSpace V Aset R f)
            (fun _ => piR b Aset (fun _ => B))),
        fun B hB => (h4 Aset R B hAset hR hB).2,
        fun hb0 _ _ => by rw [hb0]; exact piR_zero_mem_univZero⟩
    · rw [AnnotValid_lam, interp_sort]
      exact ⟨trivial, fun B hB => (h4 Aset R B hAset hR hB).1.2⟩
    · rw [interp_lam, interp_sort]
      exact lamR_mem fun B hB => (h4 Aset R B hAset hR hB).2
  have h2 : ∀ Aset : V, Aset ∈ˢ (univ u : V) →
      WellDenotedV V (cons Aset ρ)
          (.lam b quotRelTy
            (.lam b (.sort v)
              (.lam b (.pi 0 b (.bvar 2) (.bvar 1))
                (.lam b (quotLiftInvTy E)
                  (.lam b (.bvar 4) (.app (.bvar 2) (.bvar 0))))))) ∧
        interp V (cons Aset ρ)
          (.lam b quotRelTy
            (.lam b (.sort v)
              (.lam b (.pi 0 b (.bvar 2) (.bvar 1))
                (.lam b (quotLiftInvTy E)
                  (.lam b (.bvar 4) (.app (.bvar 2) (.bvar 0)))))))
          ∈ˢ piR b (relSpace V u Aset) (fun R =>
            piR b (univ v : V) (fun B =>
              piR b (piR b Aset (fun _ => B))
                (fun f => piR b (quotInvSpace V Aset R f)
                  (fun _ => piR b Aset (fun _ => B))))) := by
    intro Aset hAset
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [WellDenoted_lam, quotRelTy_interp u]
      exact ⟨(quotRelTy_wellDenotedV _).1,
        fun R hR => (h3 Aset R hAset hR).1.1,
        fun R => piR b (univ v : V) (fun B =>
          piR b (piR b Aset (fun _ => B))
            (fun f => piR b (quotInvSpace V Aset R f)
              (fun _ => piR b Aset (fun _ => B)))),
        fun R hR => (h3 Aset R hAset hR).2,
        fun hb0 _ _ => by rw [hb0]; exact piR_zero_mem_univZero⟩
    · rw [AnnotValid_lam, quotRelTy_interp u]
      exact ⟨(quotRelTy_wellDenotedV _).2,
        fun R hR => (h3 Aset R hAset hR).1.2⟩
    · rw [interp_lam, quotRelTy_interp u]
      exact lamR_mem fun R hR => (h3 Aset R hAset hR).2
  rw [quotLiftRa]
  refine ⟨?_, ?_⟩
  · rw [WellDenoted_lam, interp_sort]
    exact ⟨trivial, fun Aset hAset => (h2 Aset hAset).1.1,
      fun Aset => piR b (relSpace V u Aset) (fun R =>
        piR b (univ v : V) (fun B =>
          piR b (piR b Aset (fun _ => B))
            (fun f => piR b (quotInvSpace V Aset R f)
              (fun _ => piR b Aset (fun _ => B))))),
      fun Aset hAset => (h2 Aset hAset).2,
      fun hb0 _ _ => by rw [hb0]; exact piR_zero_mem_univZero⟩
  · rw [AnnotValid_lam, interp_sort]
    exact ⟨trivial, fun Aset hAset => (h2 Aset hAset).1.2⟩

/-! ### The two sides of the fired equality -/

/-- **`Quot.lift` fires against a class, at every numeral.**  At
`v ≠ 0` this is `quotLiftV_app_any` + `quotLiftR_app` + the
quotient's own `app_eq_of_quotClass_eq`; at `v = 0` both sides are the
canonical proof, because a `piR 0`-valued function *is* one. -/
theorem quotLiftV_fired {u v : Nat} {Aset R B f h a : V}
    (hAset : Aset ∈ˢ (univ u : V)) (hR : R ∈ˢ relSpace V u Aset)
    (hB : B ∈ˢ (univ v : V)) (hf : f ∈ˢ piR v Aset fun _ => B)
    (hh : h ∈ˢ quotInvSpace V Aset R f) (ha : a ∈ˢ Aset) :
    app (app (app (app (app (app (quotLiftV V u v) Aset) R) B) f) h)
        (quotClass u Aset R a) = app f a := by
  rw [quotLiftV_app_any V hAset hR hB hf hh]
  by_cases hv : v = 0
  · subst hv
    rw [quotLiftR, lamR_zero, app_pt, eq_pt_of_mem_piR_zero hf, app_pt]
  · rw [quotLiftR_app V hv (quotClass_mem ha)]
    obtain ⟨hrep, hcls⟩ :=
      qrep_spec (u := u) (R := R) (quotClass_mem (u := u) ha)
    exact app_eq_of_quotClass_eq hAset hrep ha (quotInv_of_mem V hh)
      hcls.symm

/-- …and the RHS tower's own six-fold application is the same value.

Note what is **absent**: the bit/level correspondence `b = 0 ↔ v = 0`.
The tower's own collapse is driven by its bit alone — at `b = 0` both
the tower and its argument `f` are the canonical proof — so the two
sides meet without ever comparing the reading's numeral to the
constant's sort.  The correspondence is needed only where the
*recursor's* value law is read (`quotLiftV_fired`'s `hf`). -/
theorem quotLiftRa_app {E : AnnotTerm} {b u v : Nat}
    (hval : ∀ (ρ' : Nat → V) (T x y : V), T ∈ˢ (univ v : V) →
      x ∈ˢ T → y ∈ˢ T →
      app (app (app (interp V ρ' E) T) x) y = eqv x y)
    (hgr : ∀ (ρ' : Nat → V) (Aa la ra : AnnotTerm),
      WellDenotedV V ρ' Aa → WellDenotedV V ρ' la → WellDenotedV V ρ' ra →
      interp V ρ' Aa ∈ˢ (univ v : V) →
      interp V ρ' la ∈ˢ interp V ρ' Aa →
      interp V ρ' ra ∈ˢ interp V ρ' Aa →
      WellDenotedV V ρ' (.app (.app (.app E Aa) la) ra) ∧
        interp V ρ' (.app (.app (.app E Aa) la) ra)
          ∈ˢ (univZero : V))
    (ρ : Nat → V) {Aset R B f h a : V}
    (hAset : Aset ∈ˢ (univ u : V)) (hR : R ∈ˢ relSpace V u Aset)
    (hB : B ∈ˢ (univ v : V)) (hf : f ∈ˢ piR b Aset fun _ => B)
    (hh : h ∈ˢ quotInvSpace V Aset R f) (ha : a ∈ˢ Aset) :
    app (app (app (app (app (app (interp V ρ (quotLiftRa E b u v))
        Aset) R) B) f) h) a = app f a := by
  by_cases hb : b = 0
  · rw [quotLiftRa, interp_lam, hb, lamR_zero, app_pt, app_pt,
      app_pt, app_pt, app_pt, app_pt]
    rw [hb] at hf
    rw [eq_pt_of_mem_piR_zero hf, app_pt]
  have hdom : interp V (cons B (cons R (cons Aset ρ)))
      (AnnotTerm.pi 0 b (.bvar 2) (.bvar 1)) = piR b Aset (fun _ => B) := by
    rw [interp_pi]; simp only [interp_bvar, cons]
  obtain ⟨hinvint, -⟩ := quotLiftInvTy_data (u := u) ρ hval hgr hR hB
    hf (fun hb0 => absurd hb0 hb)
  rw [quotLiftRa, interp_lam, interp_sort, app_lamR_pos hb hAset,
    interp_lam, quotRelTy_interp u, app_lamR_pos hb hR,
    interp_lam, interp_sort, app_lamR_pos hb hB,
    interp_lam, hdom, app_lamR_pos hb hf,
    interp_lam, hinvint, app_lamR_pos hb hh,
    interp_lam,
    show interp V (cons h (cons f (cons B (cons R (cons Aset ρ)))))
      (AnnotTerm.bvar 4) = Aset from by simp [interp_bvar, cons],
    app_lamR_pos hb ha]
  simp [interp_app, interp_bvar, cons]

/-! ### The row -/

set_option maxHeartbeats 1000000 in
/-- **`Quot.lift`'s `RecRuleLaw` row.**  The rule is `.plain`, so both
`.nested` conjuncts are `nomatch`.  The two telescope fits are peeled
with `interp_inst_cons1`..`_cons4`, which put every substituted domain
at exactly the `cons` environment its space lemma is stated at; the
fired equality is `quotLiftV_fired` against `quotLiftRa_app`; the
transport is six `WellDenotedV_app_of` steps over `quotLiftRaSpace`. -/
theorem quotLiftLaw {m : EnvModel V env}
    (m₂ : EnvModel V ⟨quotLiftA :: env.consts⟩)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hE : env.find? eqName = some eqA) (heq : EqLaw m)
    (hac : m₂.acval = acvalWith m.acval quotLiftA.name
      (fun ψ => AnnotTerm.const .quotLift [ψ uN, ψ vN]))
    (φ : Name → Nat) :
    RecRuleLaw m₂ φ quotLiftA.name quotLiftA.toConstantVal 5 5
      quotLiftRule := by
  refine ⟨Nat.le_refl 5, fun us hus => ?_⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Name → Nat,
      ψ = Level.substFn φ quotLiftA.toConstantVal.levelParams us :=
    ⟨_, rfl⟩
  have hEuN : Level.substFn ψ [uN] [Level.param vN] uN = ψ vN := by
    simp [Level.substFn, Level.eval]
  obtain ⟨hval0, hgr0⟩ :=
    heq hE (Level.substFn ψ [uN] [Level.param vN])
  rw [hEuN] at hval0 hgr0
  have hz : pwBit ψ (ConLeche.PropWhen.ifAllZero [vN]) = 0 ↔ ψ vN = 0 :=
    pwBit_ifAllZero_single ψ vN
  have hRa : denoteMeta m₂.acval ⟨quotLiftA :: env.consts⟩ φ 0
      (quotLiftRule.rhs.instantiateLevelParams
        quotLiftA.toConstantVal.levelParams us)
      = some (quotLiftRa
          (m.acval eqName (Level.substFn ψ [uN] [Level.param vN]))
          (pwBit ψ (.ifAllZero [vN])) (ψ uN) (ψ vN)) := by
    rw [denoteMeta_instLevels (acvalParamsAt_of_core m₂) φ, hac, hψ,
      denoteMeta_quotLift_rhs (m := m) _ hE]
  refine ⟨_, hRa,
    fun ρ => quotLiftRa_wellDenotedV hz hval0 hgr0 ρ, ?_, ?_⟩
  · intro _ _ h
    exact nomatch h
  intro cvj cnP cnF hfj usj ρ xs ys TVa TVja restR restC hxs hys husj
    hlev _ hnested hpin hTVa hTVja hfitR hfitC
  have hM' : (⟨quotLiftA :: env.consts⟩ : Env).find? quotMkName
      = some quotMkA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hM
  rw [show RecRule.ctor quotLiftRule = quotMkName from rfl, hM'] at hfj
  obtain ⟨rfl, rfl, rfl⟩ :
      cvj = quotMkA.toConstantVal ∧ cnP = 2 ∧ cnF = 1 := by
    injection Option.some.inj hfj with a1 a2 a3
    exact ⟨a1.symm, a2.symm, a3.symm⟩
  obtain ⟨x1, x2, x3, x4, x5, rfl⟩ :
      ∃ p q r s t, xs = [p, q, r, s, t] := by
    match xs, hxs with
    | [p, q, r, s, t], _ => exact ⟨p, q, r, s, t, rfl⟩
  obtain ⟨y1, y2, y3, rfl⟩ : ∃ p q r, ys = [p, q, r] := by
    match ys, hys with
    | [p, q, r], _ => exact ⟨p, q, r, rfl⟩
  -- the constructor's level is the recursor's own `u`
  have hulev : Level.substFn φ quotMkA.toConstantVal.levelParams usj uN
      = ψ uN := by
    rw [congrFun hlev uN, hψ]
    show Level.eval φ (Level.subst quotLiftA.toConstantVal.levelParams
      us (.param uN)) = _
    rw [Level.subst, Level.eval_subst_go]
  -- the two readings, identified
  have hTyRead : denoteMeta m₂.acval ⟨quotLiftA :: env.consts⟩ φ 0
      (quotLiftA.toConstantVal.type.instantiateLevelParams
        quotLiftA.toConstantVal.levelParams us)
      = some (quotLiftTy
          (m.acval eqName (Level.substFn ψ [uN] [Level.param vN]))
          (pwBit ψ (.ifAllZero [vN])) (ψ uN) (ψ vN)) := by
    rw [denoteMeta_instLevels (acvalParamsAt_of_core m₂) φ, hac, hψ,
      denoteMeta_quotLiftA_type (m := m) _ hQ hE]
  obtain rfl : TVa = _ :=
    (Option.some.inj (hTyRead.symm.trans hTVa)).symm
  have hCtorRead : denoteMeta m₂.acval ⟨quotLiftA :: env.consts⟩ φ 0
      (quotMkA.toConstantVal.type.instantiateLevelParams
        quotMkA.toConstantVal.levelParams usj)
      = some (quotMkTy
          (pwBit (Level.substFn φ quotMkA.toConstantVal.levelParams usj)
            (.ifAllZero [uN]))
          (Level.substFn φ quotMkA.toConstantVal.levelParams usj uN)) := by
    rw [denoteMeta_instLevels (acvalParamsAt_of_core m₂) φ, hac,
      denoteMeta_quotMkTy (m := m) _ (by decide) hQ]
  obtain rfl : TVja = _ :=
    (Option.some.inj (hCtorRead.symm.trans hTVja)).symm
  -- peel the recursor's telescope
  rw [quotLiftTy] at hfitR
  cases hfitR with | cons f1 hfitR =>
  cases hfitR with | cons f2 hfitR =>
  cases hfitR with | cons f3 hfitR =>
  cases hfitR with | cons f4 hfitR =>
  cases hfitR with | cons f5 hfitR =>
  cases hfitR with | cons f6 _ =>
  rw [interp_sort] at f1
  rw [interp_inst0, quotRelTy_interp (ψ uN)] at f2
  rw [interp_inst0, interp_inst_cons1, interp_sort] at f3
  rw [interp_inst0, interp_inst_cons1, interp_inst_cons2,
    interp_pi] at f4
  simp only [interp_bvar, cons] at f4
  rw [interp_inst0, interp_inst_cons1, interp_inst_cons2,
    interp_inst_cons3,
    (quotLiftInvTy_data (u := ψ uN) ρ hval0 hgr0 f2 f3 f4
      (fun hb0 => by
        rw [← univ_zero, ← hz.mp hb0]; exact f3)).1] at f5
  rw [interp_inst0, interp_inst_cons1, interp_inst_cons2,
    interp_inst_cons3, interp_inst_cons4,
    (quotApp_data (u := ψ uN) (i := 4) (j := 3)
      (ρ := cons (interp V ρ x5) (cons (interp V ρ x4)
        (cons (interp V ρ x3) (cons (interp V ρ x2)
          (cons (interp V ρ x1) ρ)))))
      (by simp [cons]) (by simp [cons]) f1 f2).2.2] at f6
  -- peel the constructor's telescope
  rw [quotMkTy] at hfitC
  cases hfitC with | cons g1 hfitC =>
  cases hfitC with | cons g2 hfitC =>
  cases hfitC with | cons g3 _ =>
  rw [hulev, interp_sort] at g1
  rw [interp_inst0, quotRelTy_interp (ψ uN)] at g2
  rw [interp_inst0, interp_inst_cons1] at g3
  simp only [interp_bvar, cons] at g3
  -- the two leaves
  have hrecL : m₂.acval quotLiftA.name
      (Level.substFn φ quotLiftA.toConstantVal.levelParams us)
      = AnnotTerm.const .quotLift [ψ uN, ψ vN] := by
    rw [hac, acvalWith_self, hψ]
  have hctorL0 : m₂.acval quotMkName
      (Level.substFn φ quotMkA.toConstantVal.levelParams usj)
      = AnnotTerm.const .quotMk
        [Level.substFn φ quotMkA.toConstantVal.levelParams usj uN] := by
    rw [hac, acvalWith_ne (by decide)]
    refine acval_basis_pinned (m := m) hM (by decide) ?_
    simp +decide [ConLeche.Verify.pinnedStructT]
  have hctorL : m₂.acval quotMkName
      (Level.substFn φ quotMkA.toConstantVal.levelParams usj)
      = AnnotTerm.const .quotMk [ψ uN] := by rw [hctorL0, hulev]
  -- the major premise's fit: the class formed at the CONSTRUCTOR's
  -- parameters lies in the quotient at the recursor's, which is all the
  -- rule needs — the two parameter spines are never compared
  have hmem : quotClass (ψ uN) (interp V ρ y1) (interp V ρ y2) (interp V ρ y3)
      ∈ˢ quotSet (ψ uN) (interp V ρ x1) (interp V ρ x2) := by
    simp only [show RecRule.ctor quotLiftRule = quotMkName from rfl,
      AnnotTerm.mkAppN_cons, AnnotTerm.mkAppN_nil, interp_app,
      hctorL, interp_const, bval, ConLeche.Term.lv,
      List.getD_cons_zero] at f6
    rwa [quotMkV_app V g1 g2 g3] at f6
  obtain ⟨hg3, hcls⟩ := quotClass_of_mem_quotSet f1 g1 g3 hmem
  have hfv : interp V ρ x4
      ∈ˢ piR (ψ vN) (interp V ρ x1) fun _ => interp V ρ x3 := by
    rwa [piR_zero_agree hz (fun _ _ => rfl)] at f4
  refine ⟨?_, ?_⟩
  · -- the fired equality
    simp only [show RecRule.ctor quotLiftRule = quotMkName from rfl,
      show quotLiftRule.ctorParams = 2 from rfl,
      List.take, List.drop, List.cons_append, List.nil_append,
      AnnotTerm.mkAppN_cons, AnnotTerm.mkAppN_nil, hrecL, hctorL,
      interp_app, interp_const, bval, ConLeche.Term.lv,
      List.getD_cons_zero, List.getD_cons_succ]
    rw [quotMkV_app V g1 g2 g3, hcls,
      quotLiftV_fired f1 f2 f3 hfv f5 hg3,
      quotLiftRa_app hval0 hgr0 ρ f1 f2 f3 f4 f5 hg3]
  · -- the transport
    intro hxsA hysA
    simp only [show quotLiftRule.ctorParams = 2 from rfl,
      List.take, List.drop, List.cons_append, List.nil_append,
      AnnotTerm.mkAppN_cons, AnnotTerm.mkAppN_nil]
    have hRm := quotLiftRa_mem (u := ψ uN) hz hval0 hgr0 ρ
    rw [quotLiftRaSpace] at hRm
    have h1 := WellDenotedV_app_of
      (quotLiftRa_wellDenotedV (u := ψ uN) hz hval0 hgr0 ρ)
      (hxsA x1 (by simp)) hRm f1
      (fun hb0 _ _ => by rw [hb0]; exact piR_zero_mem_univZero)
    have h2 := WellDenotedV_app_of h1.1 (hxsA x2 (by simp)) h1.2 f2
      (fun hb0 _ _ => by rw [hb0]; exact piR_zero_mem_univZero)
    have h3 := WellDenotedV_app_of h2.1 (hxsA x3 (by simp)) h2.2 f3
      (fun hb0 _ _ => by rw [hb0]; exact piR_zero_mem_univZero)
    have h4 := WellDenotedV_app_of h3.1 (hxsA x4 (by simp)) h3.2 f4
      (fun hb0 _ _ => by rw [hb0]; exact piR_zero_mem_univZero)
    have h5 := WellDenotedV_app_of h4.1 (hxsA x5 (by simp)) h4.2 f5
      (fun hb0 _ _ => by rw [hb0]; exact piR_zero_mem_univZero)
    exact (WellDenotedV_app_of h5.1 (hysA y3 (by simp)) h5.2 hg3
      (fun hb0 _ _ => by
        rw [← univ_zero, ← hz.mp hb0]; exact f3)).1

/-- The two `EqLaw` halves at the assignment `Quot.lift` reads the
`Eq` former at — `v`, not the constant's own first parameter. -/
theorem quotLift_eqLaws (mp : EnvModelM V μ env)
    (hE : env.find? eqName = some eqA) (ψ : Name → Nat) :
    (∀ (ρ : Nat → V) (T x y : V), T ∈ˢ (univ (ψ vN) : V) →
      x ∈ˢ T → y ∈ˢ T →
      app (app (app (interp V ρ (mp.base2.acval eqName
        (Level.substFn ψ [uN] [Level.param vN]))) T) x) y = eqv x y) ∧
    (∀ (ρ : Nat → V) (Aa la ra : AnnotTerm),
      WellDenotedV V ρ Aa → WellDenotedV V ρ la → WellDenotedV V ρ ra →
      interp V ρ Aa ∈ˢ (univ (ψ vN) : V) →
      interp V ρ la ∈ˢ interp V ρ Aa →
      interp V ρ ra ∈ˢ interp V ρ Aa →
      WellDenotedV V ρ (.app (.app (.app (mp.base2.acval eqName
          (Level.substFn ψ [uN] [Level.param vN])) Aa) la) ra) ∧
        interp V ρ (.app (.app (.app (mp.base2.acval eqName
          (Level.substFn ψ [uN] [Level.param vN])) Aa) la) ra)
          ∈ˢ (univZero : V)) := by
  have hEuN : Level.substFn ψ [uN] [Level.param vN] uN = ψ vN := by
    simp [Level.substFn, Level.eval]
  obtain ⟨hval0, hgr0⟩ :=
    mp.eq_law hE (Level.substFn ψ [uN] [Level.param vN])
  rw [hEuN] at hval0 hgr0
  exact ⟨hval0, hgr0⟩

/-- **`Quot.lift`, installed at the P tier.** -/
theorem extendQuotLift (mp : EnvModelM V μ env)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hE : env.find? eqName = some eqA)
    (hfresh : env.find? quotLiftA.name = none)
    (hwf : EnvWF ⟨quotLiftA :: env.consts⟩) :
    Nonempty (EnvModelM V μ ⟨quotLiftA :: env.consts⟩) := by
  have hty := fun ψ =>
    denoteMeta_quotLiftA_type (m := mp.base2)
      (A := fun ψ => AnnotTerm.const .quotLift [ψ uN, ψ vN]) ψ hQ hE
  have hz : ∀ ψ : Name → Nat,
      pwBit ψ (ConLeche.PropWhen.ifAllZero [vN]) = 0 ↔ ψ vN = 0 :=
    fun ψ => pwBit_ifAllZero_single ψ vN
  refine nonempty_of_exists (declStep_preserves_of_basis_rec_cons mp
    (A := fun ψ => AnnotTerm.const .quotLift [ψ uN, ψ vN]) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT quotLiftA.name ψ
          = some (Term.const .quotLift [ψ uN, ψ vN]) from rfl] at hp
        rw [← Option.some.inj hp]
        rfl)
      (fun _ h => nomatch h)
      (fun _ _ _ _ heq r hr => by
        injection heq with _ _ _ h4
        rw [← h4] at hr
        rcases List.mem_cons.mp hr with rfl | hr'
        · exact ⟨⟨_, _, _, hM⟩, fun hb => Bool.noConfusion hb,
            fun hb => Bool.noConfusion hb⟩
        · exact nomatch hr'))
    (fun _ _ => rfl) ?_
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_ ?_)
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by
        show uN ∈ [uN, vN]
        exact List.mem_cons_self),
      hp vN (by
        show vN ∈ [uN, vN]
        exact List.mem_cons_of_mem _ List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact quotLiftTy_wellDenotedV (hz ψ) (quotLift_eqLaws mp hE ψ).1
      (quotLift_eqLaws mp hE ψ).2 ρ
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [interp_const]
    exact quotLiftTy_mem (hz ψ) (quotLift_eqLaws mp hE ψ).1
      (quotLift_eqLaws mp hE ψ).2 ρ
  · intro m₂ hac φ
    refine recRules_cons_rec mp hfresh quotLiftA_eq m₂ hac φ ?_
    intro rl hrl _
    rcases List.mem_cons.mp hrl with rfl | hr'
    · exact quotLiftLaw (m := mp.base2) m₂ hQ hM hE mp.eq_law hac φ
    · exact nomatch hr'

/-- **The `Quot` block, installed at the P tier.**  `BasisStepPB`'s
`quotK` branch — the one branch whose `DeclBasisRun` premise is not
vacuous: `Eq` must already be stored, and that is exactly what the
`Eq` bridge consumes. -/
theorem declBasisPB_quotK {env₁ : Env} (mp : EnvModelM V μ env)
    (hEq : env.find? eqName = some eqA)
    (h : ConLeche.Semantics.BasisInstallRun env
      ConLeche.BasisKind.quotK.declsA env₁) :
    Nonempty (EnvModelM V μ env₁) := by
  rw [show ConLeche.BasisKind.quotK.declsA
    = [quotA, quotMkA, quotLiftA, quotIndA, quotSoundA] from rfl] at h
  obtain ⟨h1, h2, h3, h4, h5, hnil⟩ := h
  subst hnil
  have hf1 : env.find? quotA.name = none :=
    Option.isNone_iff_eq_none.mp h1
  have hwf1 : EnvWF ⟨quotA :: env.consts⟩ :=
    EnvWF.cons mp.base2.wf ⟨rfl, rfl, rfl, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
  obtain ⟨mp1⟩ := extendQuot mp hf1  hwf1
  have hQ1 : (⟨quotA :: env.consts⟩ : Env).find? quotName
      = some quotA := by
    rw [ConLeche.Env.find?_cons]; exact if_pos rfl
  have hE1 : (⟨quotA :: env.consts⟩ : Env).find? eqName = some eqA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hEq
  have hf2 : (⟨quotA :: env.consts⟩ : Env).find? quotMkA.name = none :=
    Option.isNone_iff_eq_none.mp h2
  have hwf2 : EnvWF ⟨quotMkA :: quotA :: env.consts⟩ := by
    refine EnvWF.cons hwf1 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
    show Expr.constsResolve _ quotMkA.toConstantVal.type = true
    have hf : (⟨quotMkA :: quotA :: env.consts⟩ : Env).find? quotName
        = some quotA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hQ1
    rw [show quotMkA.toConstantVal.type
      = Expr.forallE (.sort (.param uN))
          (Expr.forallE
            (Expr.forallE (.bvar 0)
              (Expr.forallE (.bvar 1) (.sort .zero)
                { pw := .never })
              { pw := .never })
            (Expr.forallE (.bvar 1)
              (.app (.app (.const quotName [.param uN]) (.bvar 2))
                (.bvar 1)) { pw := .ifAllZero [uN] })
            { pw := .ifAllZero [uN] })
          { pw := .ifAllZero [uN] } from rfl]
    simp [Expr.constsResolve, hf]
  obtain ⟨mp2⟩ := extendQuotMk mp1 hQ1 hf2  hwf2
  have hQ2 : (⟨quotMkA :: quotA :: env.consts⟩ : Env).find? quotName
      = some quotA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hQ1
  have hM2 : (⟨quotMkA :: quotA :: env.consts⟩ : Env).find? quotMkName
      = some quotMkA := by
    rw [ConLeche.Env.find?_cons]; exact if_pos rfl
  have hE2 : (⟨quotMkA :: quotA :: env.consts⟩ : Env).find? eqName
      = some eqA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hE1
  have hf3 : (⟨quotMkA :: quotA :: env.consts⟩ : Env).find?
      quotLiftA.name = none := Option.isNone_iff_eq_none.mp h3
  have hwf3 : EnvWF ⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ := by
    have hfQ : (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩
        : Env).find? quotName = some quotA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hQ2
    have hfE : (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩
        : Env).find? eqName = some eqA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hE2
    refine EnvWF.cons hwf2 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), ?_,
      (fun _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
    · show Expr.constsResolve _ quotLiftA.toConstantVal.type = true
      rw [show quotLiftA.toConstantVal.type
          = Expr.forallE (.sort (.param uN))
              (Expr.forallE
                (Expr.forallE (.bvar 0)
                  (Expr.forallE (.bvar 1) (.sort .zero)
                    { pw := .never })
                  { pw := .never })
                (Expr.forallE
                  (.sort (.param vN))
                  (Expr.forallE
                    (Expr.forallE (.bvar 2)
                      (.bvar 1)
                      { pw := .ifAllZero [vN] })
                    (Expr.forallE
                      (Expr.forallE (.bvar 3)
                        (Expr.forallE (.bvar 4)
                          (Expr.forallE
                            (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
                            (.app (.app (.app
                              (.const eqName [.param vN]) (.bvar 4))
                              (.app (.bvar 3) (.bvar 2)))
                              (.app (.bvar 3) (.bvar 1)))
                            { pw := .ifAllZero [] })
                          { pw := .ifAllZero [] })
                        { pw := .ifAllZero [] })
                      (Expr.forallE
                        (.app (.app (.const quotName [.param uN])
                          (.bvar 4)) (.bvar 3))
                        (.bvar 3)
                        { pw := .ifAllZero [vN] })
                      { pw := .ifAllZero [vN] })
                    { pw := .ifAllZero [vN] })
                  { pw := .ifAllZero [vN] })
                { pw := .ifAllZero [vN] })
              { pw := .ifAllZero [vN] } from rfl]
      simp [Expr.constsResolve, hfQ, hfE]
    · intro cv mI rP rules heq
      injection heq with h1' _ _ h4'
      subst h1'; subst h4'
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr'
      · exact ⟨rfl, rfl, by
          show Expr.constsResolve _ (RecRule.rhs quotLiftRule) = true
          simp [Expr.constsResolve, quotLiftRule, hfE], rfl,
          fun lvls pins heqf => nomatch heqf⟩
      · exact nomatch hr'
  obtain ⟨mp3⟩ := extendQuotLift mp2 hQ2 hM2 hE2 hf3  hwf3
  have hQ3 : (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩
      : Env).find? quotName = some quotA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hQ2
  have hM3 : (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩
      : Env).find? quotMkName = some quotMkA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hM2
  have hE3 : (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩
      : Env).find? eqName = some eqA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hE2
  have hf4 : (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩
      : Env).find? quotIndA.name = none :=
    Option.isNone_iff_eq_none.mp h4
  have hwf4 : EnvWF ⟨quotIndA :: quotLiftA :: quotMkA :: quotA
      :: env.consts⟩ := by
    have hfQ : (⟨quotIndA :: quotLiftA :: quotMkA :: quotA
        :: env.consts⟩ : Env).find? quotName = some quotA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hQ3
    have hfM : (⟨quotIndA :: quotLiftA :: quotMkA :: quotA
        :: env.consts⟩ : Env).find? quotMkName = some quotMkA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hM3
    refine EnvWF.cons hwf3 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), ?_,
      (fun _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
    · show Expr.constsResolve _ quotIndA.toConstantVal.type = true
      rw [show quotIndA.toConstantVal.type
          = Expr.forallE (.sort (.param uN))
              (Expr.forallE
                (Expr.forallE (.bvar 0)
                  (Expr.forallE (.bvar 1) (.sort .zero)
                    { pw := .never })
                  { pw := .never })
                (Expr.forallE
                  (Expr.forallE
                    (.app (.app (.const quotName [.param uN]) (.bvar 1))
                      (.bvar 0)) (.sort .zero)
                    { pw := .never })
                  (Expr.forallE
                    (Expr.forallE (.bvar 2)
                      (.app (.bvar 1)
                        (.app (.app (.app
                          (.const quotMkName [.param uN])
                          (.bvar 3)) (.bvar 2)) (.bvar 0)))
                      { pw := .ifAllZero [] })
                    (Expr.forallE
                      (.app (.app (.const quotName [.param uN])
                        (.bvar 3)) (.bvar 2))
                      (.app (.bvar 2) (.bvar 0))
                      { pw := .ifAllZero [] })
                    { pw := .ifAllZero [] })
                  { pw := .ifAllZero [] })
                { pw := .ifAllZero [] })
              { pw := .ifAllZero [] } from rfl]
      simp [Expr.constsResolve, hfQ, hfM]
    · intro cv mI rP rules heq
      injection heq with h1' _ _ h4'
      subst h1'; subst h4'
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr'
      · exact ⟨rfl, rfl, by
          show Expr.constsResolve _ (RecRule.rhs quotIndRule) = true
          simp [Expr.constsResolve, quotIndRule, hfQ, hfM], rfl,
          fun lvls pins heqf => nomatch heqf⟩
      · exact nomatch hr'
  obtain ⟨mp4⟩ := extendQuotInd mp3 hQ3 hM3 hf4  hwf4
  have hQ4 : (⟨quotIndA :: quotLiftA :: quotMkA :: quotA
      :: env.consts⟩ : Env).find? quotName = some quotA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hQ3
  have hM4 : (⟨quotIndA :: quotLiftA :: quotMkA :: quotA
      :: env.consts⟩ : Env).find? quotMkName = some quotMkA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hM3
  have hE4 : (⟨quotIndA :: quotLiftA :: quotMkA :: quotA
      :: env.consts⟩ : Env).find? eqName = some eqA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hE3
  have hf5 : (⟨quotIndA :: quotLiftA :: quotMkA :: quotA
      :: env.consts⟩ : Env).find? quotSoundA.name = none :=
    Option.isNone_iff_eq_none.mp h5
  have hwf5 : EnvWF ⟨quotSoundA :: quotIndA :: quotLiftA :: quotMkA
      :: quotA :: env.consts⟩ := by
    have hfQ : (⟨quotSoundA :: quotIndA :: quotLiftA :: quotMkA
        :: quotA :: env.consts⟩ : Env).find? quotName
        = some quotA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hQ4
    have hfM : (⟨quotSoundA :: quotIndA :: quotLiftA :: quotMkA
        :: quotA :: env.consts⟩ : Env).find? quotMkName
        = some quotMkA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hM4
    have hfE : (⟨quotSoundA :: quotIndA :: quotLiftA :: quotMkA
        :: quotA :: env.consts⟩ : Env).find? eqName = some eqA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hE4
    refine EnvWF.cons hwf4 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
    show Expr.constsResolve _ quotSoundA.toConstantVal.type = true
    rw [show quotSoundA.toConstantVal.type
        = Expr.forallE (.sort (.param uN))
            (Expr.forallE
              (Expr.forallE (.bvar 0)
                (Expr.forallE (.bvar 1) (.sort .zero)
                  { pw := .never })
                { pw := .never })
              (Expr.forallE (.bvar 1)
                (Expr.forallE (.bvar 2)
                  (Expr.forallE
                    (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
                    (.app (.app (.app (.const eqName [.param uN])
                      (.app (.app (.const quotName [.param uN])
                        (.bvar 4)) (.bvar 3)))
                      (.app (.app (.app
                        (.const quotMkName [.param uN])
                        (.bvar 4)) (.bvar 3)) (.bvar 2)))
                      (.app (.app (.app
                        (.const quotMkName [.param uN])
                        (.bvar 4)) (.bvar 3)) (.bvar 1)))
                    { pw := .ifAllZero [] })
                  { pw := .ifAllZero [] })
                { pw := .ifAllZero [] })
              { pw := .ifAllZero [] })
            { pw := .ifAllZero [] } from rfl]
    simp [Expr.constsResolve, hfQ, hfM, hfE]
  exact extendQuotSound mp4 hQ4 hM4 hE4 hf5  hwf5

end Quot

end ConLeche.Model
