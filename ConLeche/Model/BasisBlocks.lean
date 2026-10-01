module

public import ConLeche.Model.Levels
public import ConLeche.Semantics.BasisRules
/- `ConLeche.Kernel.PropWhen` seals its representation on purpose (the
`Std.HashMap` pattern, task #194): the datum's module is `public` but not
`@[expose]`d, so a `cases`-then-`rfl` proof cannot see the reduct.
`import all` restores that view HERE only. -/
import all ConLeche.Kernel.PropWhen
import ConLeche.Model.Annot.BitInst

public section

/-!
# The remaining basis blocks, P tier (task #161, ENDGAME G)

`Interp/BasisEmptyP.lean` executed the ENDGAME E/F recipe at the
smallest block and closed `BasisStepPB`'s `emptyK` branch.  This file
carries the same recipe across the other five, mirroring v1's single
`Install/BasisS.lean` rather than splitting per block — the shared
leaf-reading kit below is used at every one of them.

Three pieces of kit that `BasisEmptyP.lean` did not need, because
`Empty` binds no level parameter and `Empty.rec` has no rules:

* `denoteMeta_pinned_const` — a *leveled* pinned leaf's reading, the
  generalisation of `BasisEmptyP.lean`'s `hEc`;
* `denoteMeta_instLevels` (`Interp/LevelsP.lean`) — so that a recursor
  row's instantiated subjects (`RecRuleLaw` reads
  `rhs.instantiateLevelParams` and `cv.type.instantiateLevelParams`)
  are the *raw* readings at a substituted assignment.  One reading
  lemma per constant then serves both `EnvModelM.type_reads` and the
  row's `TVa`;
* `declStep_preserves_of_basis_rec_cons` (`Interp/BasisStepP.lean`) — the six
  collapsed rows at a recursor cons, whose seventh is bespoke.
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

/-! ## The leaf kit

`BasisEmptyP.lean`'s `hEc` at a constant that actually binds levels. -/

/-- **A stored pinned constant's reading, at a level list.**  The
extension's fresh leaf is stepped over by `acvalWith_ne`, the prefix
lookup by `Env.find?_cons`, and the leaf itself is
`acval_basis_pinned`. -/
theorem denoteMeta_pinned_const {m : EnvModel V env}
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    {n : Name} {ci : ConstantInfo} {ψ : Name → Nat} {ls : List Level}
    (hne : ¬ c₀.name = n)
    (hf : env.find? n = some ci)
    (hres : ConLeche.reservedBasisNames.contains n = true)
    (hlen : ls.length = ci.toConstantVal.levelParams.length)
    {c : ConLeche.Term.BConst} {us : List Nat}
    (hpd : ConLeche.Verify.pinnedStructT n
      (Level.substFn ψ ci.toConstantVal.levelParams ls)
        = some (Term.const c us)) (d : Nat) :
    denoteMeta (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d
        (.const n ls) = some (AnnotTerm.const c us) := by
  have hf' : (⟨c₀ :: env.consts⟩ : Env).find? n = some ci := by
    rw [ConLeche.Env.find?_cons, if_neg hne]; exact hf
  rw [denoteMeta_const hf' hlen, acvalWith_ne (fun h => hne h.symm),
    acval_basis_pinned (m := m) hf hres hpd]

/-! ### Lift-then-instantiate absorption

`TeleFitPA` peels a `.pi` by `B.inst a`, so a telescope domain that
mentions an *earlier* argument arrives as that argument's reading
lifted past the intervening binders and then instantiated.  The two
instances the basis recursors' step spaces need. -/

/-- The general absorption: lifting past `k + 1` binders and
instantiating at `k` shifts the environment down by `k`. -/
theorem interp_liftN_succ_inst (e a : AnnotTerm) (k : Nat)
    (ρ : Nat → V) :
    interp V ρ ((e.liftN (k + 1) 0).inst a k)
      = interp V (fun i => ρ (i + k)) e := by
  rw [interp_inst, interp_liftN]
  congr 1
  funext i
  show (instE k (interp V (shiftE k 0 ρ) a) ρ) (if i < 0 then i
      else i + (k + 1)) = ρ (i + k)
  rw [if_neg (Nat.not_lt_zero i)]
  show (if i + (k + 1) < k then ρ (i + (k + 1))
    else if i + (k + 1) = k then _ else ρ (i + (k + 1) - 1)) = ρ (i + k)
  rw [if_neg (by omega), if_neg (by omega),
    show i + (k + 1) - 1 = i + k from by omega]

theorem interp_liftN2_inst1 (e a : AnnotTerm) (x : V) (ρ : Nat → V) :
    interp V (cons x ρ) ((e.liftN 2 0).inst a 1) = interp V ρ e := by
  rw [interp_liftN_succ_inst (k := 1)]
  rfl

theorem interp_liftN3_inst2 (e a : AnnotTerm) (x y : V) (ρ : Nat → V) :
    interp V (cons y (cons x ρ)) ((e.liftN 3 0).inst a 2)
      = interp V ρ e := by
  rw [interp_liftN_succ_inst (k := 2)]
  rfl

/-! ## `PUnit`

Three constants, one firing rule.  The block is the recipe's second
application and the lane's first `RecRuleLaw` row. -/

section PUnit

open ConLeche (punitA punitUnitA punitRecA punitName punitUnitName)

variable {m : EnvModel V env} {A : (Name → Nat) → AnnotTerm}

/-- `PUnit`'s type reading: `Sort u`, which is `BConst.typeAV .punit
[ψ u]` on the nose. -/
theorem denoteMeta_punitA_type
    {acval : Name → (Name → Nat) → AnnotTerm} (ψ : Name → Nat) :
    denoteMeta acval ⟨punitA :: env.consts⟩ ψ 0 punitA.toConstantVal.type
      = some (BConst.typeAV .punit [ψ uN]) := by
  rw [show punitA.toConstantVal.type = Expr.sort (.param uN) from rfl,
    denoteMeta_sort]
  rfl

/-- `PUnit.unit`'s type reading: the `PUnit` leaf, which is
`BConst.typeAV .punitUnit [ψ u]` on the nose. -/
theorem denoteMeta_punitUnitA_type (ψ : Name → Nat)
    (hP : env.find? punitName = some punitA) :
    denoteMeta (acvalWith m.acval punitUnitA.name A)
        ⟨punitUnitA :: env.consts⟩ ψ 0
        punitUnitA.toConstantVal.type
      = some (BConst.typeAV .punitUnit [ψ uN]) := by
  rw [show punitUnitA.toConstantVal.type
      = Expr.const punitName [Level.param uN] from rfl]
  refine denoteMeta_pinned_const (m := m) (by decide) hP (by decide)
    (by rfl) ?_ 0
  simp +decide [ConLeche.Verify.pinnedStructT, ConLeche.Term.lv]
  show Level.substFn ψ [uN] [Level.param uN] uN = ψ uN
  simp [Level.substFn]
  rfl

/-- The pinned `PUnit`/`PUnit.unit` leaves at the `PUnit.rec`
extension, at any level. -/
theorem denoteMeta_punitRec_leaves (ψ : Name → Nat)
    (hP : env.find? punitName = some punitA)
    (hU : env.find? punitUnitName = some punitUnitA) :
    (∀ (d : Nat) (l : Level),
      denoteMeta (acvalWith m.acval punitRecA.name A)
        ⟨punitRecA :: env.consts⟩ ψ d (.const punitName [l])
        = some (AnnotTerm.const .punit [l.eval ψ])) ∧
    (∀ (d : Nat) (l : Level),
      denoteMeta (acvalWith m.acval punitRecA.name A)
        ⟨punitRecA :: env.consts⟩ ψ d (.const punitUnitName [l])
        = some (AnnotTerm.const .punitUnit [l.eval ψ])) := by
  constructor
  · intro d l
    refine denoteMeta_pinned_const (m := m) (by decide) hP (by decide)
      (by rfl) ?_ d
    simp +decide [ConLeche.Verify.pinnedStructT]
    show Level.substFn ψ [uN] [l] uN = Level.eval ψ l
    simp [Level.substFn]
  · intro d l
    refine denoteMeta_pinned_const (m := m) (by decide) hU (by decide)
      (by rfl) ?_ d
    simp +decide [ConLeche.Verify.pinnedStructT]
    show Level.substFn ψ [uN] [l] uN = Level.eval ψ l
    simp [Level.substFn]

/-- **`PUnit.rec`'s type reading.**  Three binders, three stored pins;
the numerals are `pwBit`s of exactly those pins. -/
theorem denoteMeta_punitRecA_type (ψ : Name → Nat)
    (hP : env.find? punitName = some punitA)
    (hU : env.find? punitUnitName = some punitUnitA) :
    denoteMeta (acvalWith m.acval punitRecA.name A)
        ⟨punitRecA :: env.consts⟩ ψ 0 punitRecA.toConstantVal.type
      = some (.pi 0 (pwBit ψ (.ifAllZero [u1N]))
          (.pi 0 (pwBit ψ .never) (.const .punit [ψ uN])
            (.sort (ψ u1N)))
          (.pi 0 (pwBit ψ (.ifAllZero [u1N]))
            (.app (.bvar 0) (.const .punitUnit [ψ uN]))
            (.pi 0 (pwBit ψ (.ifAllZero [u1N])) (.const .punit [ψ uN])
              (.app (.bvar 2) (.bvar 0))))) := by
  obtain ⟨hPc, hUc⟩ := denoteMeta_punitRec_leaves (m := m) (A := A) ψ hP hU
  rw [show punitRecA.toConstantVal.type
      = Expr.forallE
          (Expr.forallE
            (.const punitName [.param uN]) (.sort (.param u1N))
            { pw := .never })
          (Expr.forallE
            (.app (.bvar 0) (.const punitUnitName [.param uN]))
            (Expr.forallE
              (.const punitName [.param uN])
              (.app (.bvar 2) (.bvar 0))
              { pw := .ifAllZero [u1N] })
            { pw := .ifAllZero [u1N] })
          { pw := .ifAllZero [u1N] } from rfl]
  simp [denoteMeta_forallE, denoteMeta_sort, denoteMeta_app, denoteMeta_fvar,
    Expr.instantiate1, hPc, hUc, Level.eval]

/-- **The reading agrees with `BConst.typeAV`.**  Four codomain
numerals: three `pwBit_ifAllZero_single` at the motive level, and the
motive-space binder's `pwBit_never` against `v + 1`. -/
theorem bitAgree_punitRecA (ψ : Name → Nat) :
    AnnotTerm.BitAgree
      (.pi 0 (pwBit ψ (.ifAllZero [u1N]))
        (.pi 0 (pwBit ψ .never) (.const .punit [ψ uN])
          (.sort (ψ u1N)))
        (.pi 0 (pwBit ψ (.ifAllZero [u1N]))
          (.app (.bvar 0) (.const .punitUnit [ψ uN]))
          (.pi 0 (pwBit ψ (.ifAllZero [u1N])) (.const .punit [ψ uN])
            (.app (.bvar 2) (.bvar 0)))))
      (BConst.typeAV .punitRec [ψ uN, ψ u1N]) := by
  have hz : pwBit ψ (ConLeche.PropWhen.ifAllZero [u1N]) = 0 ↔ ψ u1N = 0 :=
    pwBit_ifAllZero_single ψ u1N
  refine .pi hz (.pi ?_ (.const _ _) (.sort _))
    (.pi hz (.app (.bvar 0) (.const _ _))
      (.pi hz (.const _ _) (.app (.bvar 2) (.bvar 0))))
  rw [pwBit_never]
  simp

/-! ### The block's one firing rule -/

/-- `PUnit.rec`'s single stored rule, named. -/
def punitRecRule : RecRule :=
  { ctor := punitUnitName, nfields := 0, ctorParams := 0,
    fire := .plain, eta := true, paramsBlind := true,
    rhs := Expr.lam
      (Expr.forallE
        (.const punitName [.param uN]) (.sort (.param u1N))
        { pw := .never })
      (Expr.lam
        (.app (.bvar 0) (.const punitUnitName [.param uN]))
        (.bvar 0) { pw := .ifAllZero [u1N] })
      { pw := .ifAllZero [u1N] } }

theorem punitRecA_eq :
    punitRecA = .recInfo punitRecA.toConstantVal 2 2 [punitRecRule] := by
  rfl

/-- **`PUnit.rec`'s rule's RHS reading**, at any assignment. -/
theorem denoteMeta_punitRec_rhs (ψ : Name → Nat)
    (hP : env.find? punitName = some punitA)
    (hU : env.find? punitUnitName = some punitUnitA) :
    denoteMeta (acvalWith m.acval punitRecA.name A)
        ⟨punitRecA :: env.consts⟩ ψ 0 punitRecRule.rhs
      = some (.lam (pwBit ψ (.ifAllZero [u1N]))
          (.pi 0 (pwBit ψ .never) (.const .punit [ψ uN])
            (.sort (ψ u1N)))
          (.lam (pwBit ψ (.ifAllZero [u1N]))
            (.app (.bvar 0) (.const .punitUnit [ψ uN]))
            (.bvar 0))) := by
  obtain ⟨hPc, hUc⟩ := denoteMeta_punitRec_leaves (m := m) (A := A) ψ hP hU
  rw [show punitRecRule.rhs = Expr.lam
      (Expr.forallE
        (.const punitName [.param uN]) (.sort (.param u1N))
        { pw := .never })
      (Expr.lam
        (.app (.bvar 0) (.const punitUnitName [.param uN]))
        (.bvar 0) { pw := .ifAllZero [u1N] })
      { pw := .ifAllZero [u1N] } from rfl]
  simp [denoteMeta_lam, denoteMeta_forallE, denoteMeta_sort, denoteMeta_app,
    denoteMeta_fvar, Expr.instantiate1, hPc, hUc, Level.eval]

/-- `PUnit.rec`'s rule's RHS reading, named. -/
def punitRa (ψ : Name → Nat) : AnnotTerm :=
  .lam (pwBit ψ (.ifAllZero [u1N]))
    (.pi 0 (pwBit ψ .never) (.const .punit [ψ uN]) (.sort (ψ u1N)))
    (.lam (pwBit ψ (.ifAllZero [u1N]))
      (.app (.bvar 0) (.const .punitUnit [ψ uN])) (.bvar 0))

theorem punitRa_interp (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (punitRa ψ)
      = lamR (pwBit ψ (.ifAllZero [u1N]))
          (piR 1 (unitSet : V) fun _ => univ (ψ u1N))
          (fun M => lamR (pwBit ψ (.ifAllZero [u1N])) (app M pt)
            fun z => z) := by
  simp [punitRa, interp_lam, interp_pi, interp_app, interp_bvar,
    interp_const, interp_sort, cons, pwBit_never, bval]

/-- `PUnit.rec`'s RHS reading is graded, at every environment. -/
theorem punitRa_wellDenotedV (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenotedV V ρ (punitRa ψ) := by
  constructor
  · refine ⟨⟨trivial, fun _ _ => trivial⟩, fun M hM => ?_, ?_⟩
    · refine ⟨⟨trivial, trivial, 1, unitSet, fun _ => univ (ψ u1N),
        ?_, pt_mem_unitSet, fun h => absurd h Nat.one_ne_zero⟩,
        fun _ _ => trivial, ?_⟩
      · simpa [interp_bvar, cons, interp_pi, interp_const,
          interp_sort, pwBit_never, bval] using hM
      · refine ⟨fun x => interp V (cons M ρ)
            (.app (.bvar 0) (.const .punitUnit [ψ uN])),
          fun x hx => by simpa [interp_bvar, cons] using hx,
          fun hz x _ => ?_⟩
        have hMp : app M pt ∈ˢ (univ (ψ u1N) : V) := by
          refine app_mem_piR_pos (A := (unitSet : V))
            (B := fun _ => univ (ψ u1N)) Nat.one_ne_zero ?_
            (pt_mem_unitSet (V := V))
          simpa [interp_pi, interp_const, interp_sort, pwBit_never,
            bval] using hM
        rw [(pwBit_ifAllZero_single ψ u1N).mp hz, univ_zero] at hMp
        simpa [interp_app, interp_bvar, interp_const, cons, bval]
          using hMp
    · refine ⟨fun M => piR (pwBit ψ (.ifAllZero [u1N])) (app M pt)
          (fun _ => app M pt),
        fun M hM => ?_,
        fun hz M hM => by rw [hz]; exact piR_zero_mem_univZero⟩
      have : interp V (cons M ρ)
          (AnnotTerm.lam (pwBit ψ (.ifAllZero [u1N]))
            (.app (.bvar 0) (.const .punitUnit [ψ uN])) (.bvar 0))
          = lamR (pwBit ψ (.ifAllZero [u1N])) (app M pt) fun z => z := by
        simp [interp_lam, interp_app, interp_bvar, interp_const,
          cons, bval]
      rw [this]
      exact lamR_mem fun _ hx => hx
  · exact ⟨⟨trivial, fun _ _ => trivial, fun h => nomatch h⟩,
      fun _ _ => ⟨⟨trivial, trivial⟩, fun _ _ => trivial⟩⟩

/-- **`PUnit.rec`'s `RecRuleLaw` row.**  The basis tier's first, and
`.plain` (ENDGAME F §3), so both `.nested` conjuncts are vacuous and
the live content is the fired equality — `punitRecV_app` against two
`app_lamR_pos` — plus the transport.

The `v = 0` branch is not a special case that needed a lemma: at a
`Prop`-valued motive `punitRecV_app`'s own squash regime and the
reading's `lamR 0 = pt` land on the same point, and `mem_univ_zero`
identifies the minor premise with it. -/
theorem punitRecLaw {m : EnvModel V env}
    (m₂ : EnvModel V ⟨punitRecA :: env.consts⟩)
    (hP : env.find? punitName = some punitA)
    (hU : env.find? punitUnitName = some punitUnitA)
    (hac : m₂.acval = acvalWith m.acval punitRecA.name
      (fun ψ => AnnotTerm.const .punitRec [ψ uN, ψ u1N]))
    (φ : Name → Nat) :
    RecRuleLaw m₂ φ punitRecA.name punitRecA.toConstantVal 2 2
      punitRecRule := by
  refine ⟨Nat.le_refl 2, fun us hus => ?_⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Name → Nat,
      ψ = Level.substFn φ punitRecA.toConstantVal.levelParams us :=
    ⟨_, rfl⟩
  have hRa : denoteMeta m₂.acval ⟨punitRecA :: env.consts⟩ φ 0
      (punitRecRule.rhs.instantiateLevelParams
        punitRecA.toConstantVal.levelParams us)
      = some (punitRa ψ) := by
    rw [denoteMeta_instLevels (acvalParamsAt_of_core m₂) φ, hac, hψ,
      denoteMeta_punitRec_rhs (m := m) _ hP hU]
    rfl
  refine ⟨punitRa ψ, hRa, punitRa_wellDenotedV ψ, ?_, ?_⟩
  · intro _ _ h
    exact nomatch h
  intro cvj cnP cnF hfj usj ρ xs ys TVa TVja restR restC hxs hys husj
    hlev _ hnested hpin hTVa hTVja hfitR hfitC
  -- the rule's constructor is `PUnit.unit`, stored in the prefix
  have hU' : (⟨punitRecA :: env.consts⟩ : Env).find? punitUnitName
      = some punitUnitA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hU
  rw [show RecRule.ctor punitRecRule = punitUnitName from rfl, hU']
    at hfj
  obtain ⟨rfl, rfl, rfl⟩ :
      cvj = punitUnitA.toConstantVal ∧ cnP = 0 ∧ cnF = 0 := by
    injection Option.some.inj hfj with a1 a2 a3
    exact ⟨a1.symm, a2.symm, a3.symm⟩
  obtain rfl : ys = [] := List.eq_nil_of_length_eq_zero hys
  obtain ⟨M, mm, rfl⟩ : ∃ a b, xs = [a, b] := by
    match xs, hxs with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  -- the two leaves the conclusion mentions
  have hrecL : m₂.acval punitRecA.name
      (Level.substFn φ punitRecA.toConstantVal.levelParams us)
      = AnnotTerm.const .punitRec [ψ uN, ψ u1N] := by
    rw [hac, acvalWith_self, hψ]
  have hctorL : m₂.acval punitUnitName
      (Level.substFn φ punitUnitA.toConstantVal.levelParams usj)
      = AnnotTerm.const .punitUnit
        [Level.substFn φ punitUnitA.toConstantVal.levelParams usj uN] := by
    rw [hac, acvalWith_ne (by decide)]
    refine acval_basis_pinned (m := m) hU (by decide) ?_
    simp +decide [ConLeche.Verify.pinnedStructT]
  -- the recursor's own type, identified with the given reading
  obtain rfl : TVa = .pi 0 (pwBit ψ (.ifAllZero [u1N]))
      (.pi 0 (pwBit ψ .never) (.const .punit [ψ uN]) (.sort (ψ u1N)))
      (.pi 0 (pwBit ψ (.ifAllZero [u1N]))
        (.app (.bvar 0) (.const .punitUnit [ψ uN]))
        (.pi 0 (pwBit ψ (.ifAllZero [u1N])) (.const .punit [ψ uN])
          (.app (.bvar 2) (.bvar 0)))) := by
    rw [denoteMeta_instLevels (acvalParamsAt_of_core m₂) φ, hac,
      denoteMeta_punitRecA_type (m := m) _ hP hU, ← hψ] at hTVa
    exact (Option.some.inj hTVa).symm
  -- the fit's two memberships
  cases hfitR with | cons h1 hfitR =>
  cases hfitR with | cons h2 hfitR =>
  have hM : interp V ρ M ∈ˢ piR 1 (unitSet : V)
      fun _ => univ (ψ u1N) := by
    simpa [interp_pi, interp_const, interp_sort, pwBit_never, bval]
      using h1
  have hm : interp V ρ mm ∈ˢ app (interp V ρ M) (pt : V) := by
    simpa [AnnotTerm.inst, AnnotTerm.liftN_zero, interp_app, interp_bvar,
      interp_const, cons, bval] using h2
  have hMpt : app (interp V ρ M) (pt : V) ∈ˢ (univ (ψ u1N) : V) :=
    app_mem_piR_pos (A := (unitSet : V)) (B := fun _ => univ (ψ u1N))
      Nat.one_ne_zero hM (pt_mem_unitSet (V := V))
  have hMmot : interp V ρ M ∈ˢ punitMotiveSpace V (ψ u1N) := by
    rw [punitMotiveSpace,
      ← piR_zero_agree (v := 1) (v' := ψ u1N + 1)
        (show (1 : Nat) = 0 ↔ ψ u1N + 1 = 0 by simp) (fun _ _ => rfl)]
    exact hM
  refine ⟨?_, ?_⟩
  · -- the fired equality
    simp only [show RecRule.ctor punitRecRule = punitUnitName from rfl,
      show punitRecRule.ctorParams = 0 from rfl,
      List.take, List.drop, List.cons_append, List.nil_append,
      List.append_nil, AnnotTerm.mkAppN_cons, AnnotTerm.mkAppN_nil,
      hrecL, hctorL, interp_app, interp_const, bval, ConLeche.Term.lv,
      List.getD_cons_zero, List.getD_cons_succ]
    rw [punitRecV_app V hMmot hm (pt_mem_unitSet (V := V)),
      punitRa_interp]
    by_cases hz : pwBit ψ (ConLeche.PropWhen.ifAllZero [u1N]) = 0
    · rw [hz, lamR_zero, app_pt, app_pt]
      rw [(pwBit_ifAllZero_single ψ u1N).mp hz] at hMpt
      exact mem_univ_zero hMpt hm
    · rw [app_lamR_pos hz hM, app_lamR_pos hz hm]
  · -- the transport
    intro hxsA _
    have hMA : WellDenotedV V ρ M := hxsA M (by simp)
    have hmA : WellDenotedV V ρ mm := hxsA mm (by simp)
    have hRm : interp V ρ (punitRa ψ)
        ∈ˢ piR (pwBit ψ (.ifAllZero [u1N]))
          (piR 1 (unitSet : V) fun _ => univ (ψ u1N))
          (fun M' => piR (pwBit ψ (.ifAllZero [u1N])) (app M' pt)
            fun _ => app M' pt) := by
      rw [punitRa_interp]
      exact lamR_mem fun _ _ => lamR_mem fun _ hx => hx
    have hfib : pwBit ψ (ConLeche.PropWhen.ifAllZero [u1N]) = 0 →
        ∀ x, x ∈ˢ (piR 1 (unitSet : V) fun _ => univ (ψ u1N)) →
          piR (pwBit ψ (.ifAllZero [u1N])) (app x pt)
            (fun _ => app x pt) ∈ˢ (univZero : V) := by
      intro hz _ _
      rw [hz]; exact piR_zero_mem_univZero
    have hstep : app (interp V ρ (punitRa ψ)) (interp V ρ M)
        ∈ˢ piR (pwBit ψ (.ifAllZero [u1N])) (app (interp V ρ M) pt)
          (fun _ => app (interp V ρ M) pt) :=
      app_mem_piR hRm hM hfib
    simp only [List.take, show punitRecRule.ctorParams = 0 from rfl]
    refine ⟨⟨⟨punitRa_wellDenotedV ψ ρ |>.1, hMA.1, _, _, _, hRm, hM, hfib⟩,
      hmA.1, _, _, _, hstep, hm, ?_⟩,
      ⟨⟨(punitRa_wellDenotedV ψ ρ).2, hMA.2⟩, hmA.2⟩⟩
    intro hz _ _
    rw [(pwBit_ifAllZero_single ψ u1N).mp hz, univ_zero] at hMpt
    exact hMpt

/-! ### The three installs -/

/-- **`PUnit`, installed at the P tier.** -/
theorem extendPUnit (mp : EnvModelM V μ env)
    (hfresh : env.find? punitName = none)
    (hwf : EnvWF ⟨punitA :: env.consts⟩) :
    Nonempty (EnvModelM V μ ⟨punitA :: env.consts⟩) := by
  refine nonempty_of_exists (declStep_preserves_of_basis_cons mp
    (A := fun ψ => AnnotTerm.const .punit [ψ uN]) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT punitA.name ψ
          = some (Term.const .punit [ψ uN]) from rfl] at hp
        rw [← Option.some.inj hp]
        rfl)
      (fun _ h => nomatch h) (fun _ _ _ _ h => nomatch h))
    (fun _ _ => rfl) ?_
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, denoteMeta_punitA_type ψ⟩) ?_ ?_)
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [denoteMeta_punitA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact WellDenotedV_bconst_type V .punit [ψ uN] ρ
  · intro ψ ta h ρ
    rw [denoteMeta_punitA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact bval_mem_type V .punit [ψ uN] ρ

/-- **`PUnit.unit`, installed at the P tier.** -/
theorem extendPUnitUnit (mp : EnvModelM V μ env)
    (hP : env.find? punitName = some punitA)
    (hfresh : env.find? punitUnitName = none)
    (hwf : EnvWF ⟨punitUnitA :: env.consts⟩) :
    Nonempty (EnvModelM V μ ⟨punitUnitA :: env.consts⟩) := by
  have hty := fun ψ =>
    denoteMeta_punitUnitA_type (m := mp.base2)
      (A := fun ψ => AnnotTerm.const .punitUnit [ψ uN]) ψ hP
  refine nonempty_of_exists (declStep_preserves_of_basis_cons mp
    (A := fun ψ => AnnotTerm.const .punitUnit [ψ uN]) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT punitUnitA.name ψ
          = some (Term.const .punitUnit [ψ uN]) from rfl] at hp
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
    exact WellDenotedV_bconst_type V .punitUnit [ψ uN] ρ
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact bval_mem_type V .punitUnit [ψ uN] ρ

/-- **`PUnit.rec`, installed at the P tier** — the lane's first
recursor cons: six rows collapse, the seventh is `punitRecLaw`. -/
theorem extendPUnitRec (mp : EnvModelM V μ env)
    (hP : env.find? punitName = some punitA)
    (hU : env.find? punitUnitName = some punitUnitA)
    (hfresh : env.find? punitRecA.name = none)
    (hwf : EnvWF ⟨punitRecA :: env.consts⟩) :
    Nonempty (EnvModelM V μ ⟨punitRecA :: env.consts⟩) := by
  have hty := fun ψ =>
    denoteMeta_punitRecA_type (m := mp.base2)
      (A := fun ψ => AnnotTerm.const .punitRec [ψ uN, ψ u1N]) ψ hP hU
  refine nonempty_of_exists (declStep_preserves_of_basis_rec_cons mp
    (A := fun ψ => AnnotTerm.const .punitRec [ψ uN, ψ u1N]) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT punitRecA.name ψ
          = some (Term.const .punitRec [ψ uN, ψ u1N]) from rfl] at hp
        rw [← Option.some.inj hp]
        rfl)
      (fun _ h => nomatch h)
      (fun _ _ _ _ heq r hr => by
        injection heq with _ _ _ h4
        rw [← h4] at hr
        rcases List.mem_cons.mp hr with rfl | hr'
        · exact ⟨⟨_, _, _, hU⟩, fun hb => Bool.noConfusion hb,
            fun _ => recRuleEtaOf_of hU rfl hP rfl rfl rfl rfl⟩
        · exact nomatch hr'))
    (fun _ _ => rfl) ?_
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_ ?_)
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by
        show uN ∈ [u1N, uN]
        exact List.mem_cons_of_mem _ List.mem_cons_self),
      hp u1N (by show u1N ∈ [u1N, uN]; exact List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact (bitAgree_wellDenotedV (bitAgree_punitRecA ψ) ρ).mpr
      (WellDenotedV_bconst_type V .punitRec [ψ uN, ψ u1N] ρ)
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [AnnotTerm.BitAgree.interp_eq V (bitAgree_punitRecA ψ) ρ]
    exact bval_mem_type V .punitRec [ψ uN, ψ u1N] ρ
  · intro m₂ hac φ
    refine recRules_cons_rec mp hfresh punitRecA_eq m₂ hac φ ?_
    intro rl hrl _
    rcases List.mem_cons.mp hrl with rfl | hr'
    · exact punitRecLaw (m := mp.base2) m₂ hP hU hac φ
    · exact nomatch hr'

/-- **The `PUnit` block, installed at the P tier.**  `BasisStepPB`'s
`punitK` branch — the two lanes in lockstep, exactly as
`declBasisPB_emptyK`. -/
theorem declBasisPB_punitK {env₂ : Env} (mp : EnvModelM V μ env)
    (h : ConLeche.Semantics.BasisInstallRun env
      ConLeche.BasisKind.punitK.declsA env₂) :
    Nonempty (EnvModelM V μ env₂) := by
  rw [show ConLeche.BasisKind.punitK.declsA
    = [punitA, punitUnitA, punitRecA] from rfl] at h
  obtain ⟨h1, h2, h3, hnil⟩ := h
  subst hnil
  have hf1 : env.find? punitA.name = none :=
    Option.isNone_iff_eq_none.mp h1
  have hwf1 : EnvWF ⟨punitA :: env.consts⟩ :=
    EnvWF.cons mp.base2.wf ⟨rfl, rfl, rfl, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
  obtain ⟨mp1⟩ := extendPUnit mp hf1  hwf1
  have hP1 : (⟨punitA :: env.consts⟩ : Env).find? punitName
      = some punitA := by
    rw [ConLeche.Env.find?_cons]; exact if_pos rfl
  have hf2 : (⟨punitA :: env.consts⟩ : Env).find? punitUnitA.name
      = none := Option.isNone_iff_eq_none.mp h2
  have hwf2 : EnvWF ⟨punitUnitA :: punitA :: env.consts⟩ := by
    refine EnvWF.cons hwf1 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
    show Expr.constsResolve _ punitUnitA.toConstantVal.type = true
    have hf : (⟨punitUnitA :: punitA :: env.consts⟩ : Env).find?
        punitName = some punitA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hP1
    simp only [show punitUnitA.toConstantVal.type
        = Expr.const punitName [.param uN] from rfl,
      Expr.constsResolve, hf]
    rfl
  obtain ⟨mp2⟩ := extendPUnitUnit mp1 hP1 hf2  hwf2
  have hP2 : (⟨punitUnitA :: punitA :: env.consts⟩ : Env).find?
      punitName = some punitA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hP1
  have hU2 : (⟨punitUnitA :: punitA :: env.consts⟩ : Env).find?
      punitUnitName = some punitUnitA := by
    rw [ConLeche.Env.find?_cons]; exact if_pos rfl
  have hf3 : (⟨punitUnitA :: punitA :: env.consts⟩ : Env).find?
      punitRecA.name = none := Option.isNone_iff_eq_none.mp h3
  have hfP : (⟨punitRecA :: punitUnitA :: punitA :: env.consts⟩
      : Env).find? punitName = some punitA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hP2
  have hfU : (⟨punitRecA :: punitUnitA :: punitA :: env.consts⟩
      : Env).find? punitUnitName = some punitUnitA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hU2
  have hwf3 : EnvWF
      ⟨punitRecA :: punitUnitA :: punitA :: env.consts⟩ := by
    refine EnvWF.cons hwf2 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), ?_,
      (fun _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
    · show Expr.constsResolve _ punitRecA.toConstantVal.type = true
      rw [show punitRecA.toConstantVal.type
          = Expr.forallE
              (Expr.forallE
                (.const punitName [.param uN]) (.sort (.param u1N))
                { pw := .never })
              (Expr.forallE
                (.app (.bvar 0) (.const punitUnitName [.param uN]))
                (Expr.forallE
                  (.const punitName [.param uN])
                  (.app (.bvar 2) (.bvar 0))
                  { pw := .ifAllZero [u1N] })
                { pw := .ifAllZero [u1N] })
              { pw := .ifAllZero [u1N] } from rfl]
      simp only [Expr.constsResolve, hfP, hfU, Option.isSome_some,
        Bool.and_self]
    · intro cv mI rP rules heq
      injection heq with h1' h2' h3' h4'
      subst h4'
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr'
      · refine ⟨rfl, ?_, ?_, rfl, fun lvls pins heqf => nomatch heqf⟩
        · subst h1'; rfl
        · show Expr.constsResolve _ punitRecRule.rhs = true
          rw [show punitRecRule.rhs = Expr.lam

              (Expr.forallE
                (.const punitName [.param uN]) (.sort (.param u1N))
                { pw := .never })
              (Expr.lam
                (.app (.bvar 0) (.const punitUnitName [.param uN]))
                (.bvar 0) { pw := .ifAllZero [u1N] })
              { pw := .ifAllZero [u1N] } from rfl]
          simp only [Expr.constsResolve, hfP, hfU, Option.isSome_some,
            Bool.and_self]
      · exact nomatch hr'
  exact extendPUnitRec mp2 hP2 hU2 hf3  hwf3

end PUnit

/-! ## `Nat`

Four constants, two firing rules, and the block's one bespoke row that
is not a firing law: `nat_heads`, at the cons where the literal guard
*becomes* true.  The level question does not arise at the constructors
— `Nat.zero` and `Nat.succ` bind no level parameter — so a fired rule's
`usj` is forced to `[]`. -/

section Nat

open ConLeche (natA natZeroA natSuccA natRecA natName natZeroName
  natSuccName)

variable {m : EnvModel V env} {A : (Name → Nat) → AnnotTerm}

/-- `Nat`'s type reading: `Sort 1`, `BConst.typeAV .nat []` on the
nose. -/
theorem denoteMeta_natA_type
    {acval : Name → (Name → Nat) → AnnotTerm} (ψ : Name → Nat) :
    denoteMeta acval ⟨natA :: env.consts⟩ ψ 0 natA.toConstantVal.type
      = some (BConst.typeAV .nat []) := by
  rw [show natA.toConstantVal.type = Expr.sort (.succ .zero) from rfl,
    denoteMeta_sort]
  rfl

/-- The pinned `Nat` leaf at an extension. -/
theorem denoteMeta_natLeaf {c₀ : ConstantInfo} (ψ : Name → Nat)
    (hne : ¬ c₀.name = natName)
    (hN : env.find? natName = some natA) (d : Nat) :
    denoteMeta (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d
        (.const natName []) = some (AnnotTerm.const .nat []) := by
  refine denoteMeta_pinned_const (m := m) hne hN (by decide) (by rfl) ?_ d
  simp +decide [ConLeche.Verify.pinnedStructT]

/-- `Nat.zero`'s type reading. -/
theorem denoteMeta_natZeroA_type (ψ : Name → Nat)
    (hN : env.find? natName = some natA) :
    denoteMeta (acvalWith m.acval natZeroA.name A)
        ⟨natZeroA :: env.consts⟩ ψ 0 natZeroA.toConstantVal.type
      = some (BConst.typeAV .natZero []) := by
  rw [show natZeroA.toConstantVal.type = Expr.const natName [] from rfl]
  exact denoteMeta_natLeaf (m := m) (A := A) ψ (by decide) hN 0

/-- `Nat.succ`'s type reading — one binder, pinned `.never`, so the
numeral is `1` on both sides.  Stated at *any* extension whose cons is
not `Nat`, because the `Nat.rec` row reads it too (its rule's
constructor is `Nat.succ`). -/
theorem denoteMeta_natSuccTy {c₀ : ConstantInfo} (ψ : Name → Nat)
    (hne : ¬ c₀.name = natName)
    (hN : env.find? natName = some natA) :
    denoteMeta (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ 0
        natSuccA.toConstantVal.type
      = some (.pi 0 (pwBit ψ .never) (.const .nat [])
          (.const .nat [])) := by
  have hNc := fun d => denoteMeta_natLeaf (m := m) (A := A) (c₀ := c₀)
    ψ hne hN d
  rw [show natSuccA.toConstantVal.type
      = Expr.forallE (.const natName [])
          (.const natName []) { pw := .never } from rfl]
  simp [denoteMeta_forallE, Expr.instantiate1, hNc]

theorem denoteMeta_natSuccA_type (ψ : Name → Nat)
    (hN : env.find? natName = some natA) :
    denoteMeta (acvalWith m.acval natSuccA.name A)
        ⟨natSuccA :: env.consts⟩ ψ 0 natSuccA.toConstantVal.type
      = some (.pi 0 (pwBit ψ .never) (.const .nat [])
          (.const .nat [])) :=
  denoteMeta_natSuccTy (m := m) (A := A) ψ (by decide) hN

theorem bitAgree_natSuccA (ψ : Name → Nat) :
    AnnotTerm.BitAgree
      (.pi 0 (pwBit ψ .never) (.const .nat []) (.const .nat []))
      (BConst.typeAV .natSucc []) := by
  refine .pi ?_ (.const _ _) (.const _ _)
  rw [pwBit_never]

/-- The three pinned `Nat` leaves at the `Nat.rec` extension. -/
theorem denoteMeta_natRec_leaves (ψ : Name → Nat)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA) :
    (∀ d : Nat, denoteMeta (acvalWith m.acval natRecA.name A)
        ⟨natRecA :: env.consts⟩ ψ d (.const natName [])
        = some (AnnotTerm.const .nat [])) ∧
    (∀ d : Nat, denoteMeta (acvalWith m.acval natRecA.name A)
        ⟨natRecA :: env.consts⟩ ψ d (.const natZeroName [])
        = some (AnnotTerm.const .natZero [])) ∧
    (∀ d : Nat, denoteMeta (acvalWith m.acval natRecA.name A)
        ⟨natRecA :: env.consts⟩ ψ d (.const natSuccName [])
        = some (AnnotTerm.const .natSucc [])) := by
  refine ⟨fun d => denoteMeta_natLeaf (m := m) (A := A) ψ (by decide) hN d,
    fun d => ?_, fun d => ?_⟩
  · refine denoteMeta_pinned_const (m := m) (by decide) hZ (by decide)
      (by rfl) ?_ d
    simp +decide [ConLeche.Verify.pinnedStructT]
  · refine denoteMeta_pinned_const (m := m) (by decide) hS (by decide)
      (by rfl) ?_ d
    simp +decide [ConLeche.Verify.pinnedStructT]

/-- **`Nat.rec`'s type reading.**  Seven binders; six carry
`.ifAllZero [u]` and the motive's domain carries `.never`. -/
theorem denoteMeta_natRecA_type (ψ : Name → Nat)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA) :
    denoteMeta (acvalWith m.acval natRecA.name A)
        ⟨natRecA :: env.consts⟩ ψ 0 natRecA.toConstantVal.type
      = some (.pi 0 (pwBit ψ (.ifAllZero [uN]))
          (.pi 0 (pwBit ψ .never) (.const .nat []) (.sort (ψ uN)))
          (.pi 0 (pwBit ψ (.ifAllZero [uN]))
            (.app (.bvar 0) (.const .natZero []))
            (.pi 0 (pwBit ψ (.ifAllZero [uN]))
              (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.const .nat [])
                (.pi 0 (pwBit ψ (.ifAllZero [uN]))
                  (.app (.bvar 2) (.bvar 0))
                  (.app (.bvar 3)
                    (.app (.const .natSucc []) (.bvar 1)))))
              (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.const .nat [])
                (.app (.bvar 3) (.bvar 0)))))) := by
  obtain ⟨hNc, hZc, hSc⟩ :=
    denoteMeta_natRec_leaves (m := m) (A := A) ψ hN hZ hS
  rw [show natRecA.toConstantVal.type
      = Expr.forallE
          (Expr.forallE (.const natName [])
            (.sort (.param uN)) { pw := .never })
          (Expr.forallE
            (.app (.bvar 0) (.const natZeroName []))
            (Expr.forallE
              (Expr.forallE (.const natName [])
                (Expr.forallE
                  (.app (.bvar 2) (.bvar 0))
                  (.app (.bvar 3)
                    (.app (.const natSuccName []) (.bvar 1)))
                  { pw := .ifAllZero [uN] })
                { pw := .ifAllZero [uN] })
              (Expr.forallE (.const natName [])
                (.app (.bvar 3) (.bvar 0))
                { pw := .ifAllZero [uN] })
              { pw := .ifAllZero [uN] })
            { pw := .ifAllZero [uN] })
          { pw := .ifAllZero [uN] } from rfl]
  simp [denoteMeta_forallE, denoteMeta_sort, denoteMeta_app, denoteMeta_fvar,
    Expr.instantiate1, hNc, hZc, hSc, Level.eval]

theorem bitAgree_natRecA (ψ : Name → Nat) :
    AnnotTerm.BitAgree
      (.pi 0 (pwBit ψ (.ifAllZero [uN]))
        (.pi 0 (pwBit ψ .never) (.const .nat []) (.sort (ψ uN)))
        (.pi 0 (pwBit ψ (.ifAllZero [uN]))
          (.app (.bvar 0) (.const .natZero []))
          (.pi 0 (pwBit ψ (.ifAllZero [uN]))
            (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.const .nat [])
              (.pi 0 (pwBit ψ (.ifAllZero [uN]))
                (.app (.bvar 2) (.bvar 0))
                (.app (.bvar 3)
                  (.app (.const .natSucc []) (.bvar 1)))))
            (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.const .nat [])
              (.app (.bvar 3) (.bvar 0))))))
      (BConst.typeAV .natRec [ψ uN]) := by
  have hz : pwBit ψ (ConLeche.PropWhen.ifAllZero [uN]) = 0 ↔ ψ uN = 0 :=
    pwBit_ifAllZero_single ψ uN
  refine .pi hz (.pi ?_ (.const _ _) (.sort _))
    (.pi hz (.app (.bvar 0) (.const _ _))
      (.pi hz
        (.pi hz (.const _ _)
          (.pi hz (.app (.bvar 2) (.bvar 0))
            (.app (.bvar 3) (.app (.const _ _) (.bvar 1)))))
        (.pi hz (.const _ _) (.app (.bvar 3) (.bvar 0)))))
  rw [pwBit_never]
  simp

/-! ### The installs

The first three conses are exactly the three names `nat_heads`'s guard
reads, so `natHeads_cons_offNat` is unavailable at every one of them
(`declStep_preserves_of_basis_cons_gen`).  At `Nat` and `Nat.zero` the guard is
still *false* — `Nat.succ` is not stored yet — and the row is vacuous;
at `Nat.succ` the guard becomes true and the row is the block's one
bespoke non-firing obligation, two memberships. -/

/-- **`Nat`, installed at the P tier.** -/
theorem extendNat (mp : EnvModelM V μ env)
    (hfresh : env.find? natName = none)
    (hguard : ConLeche.natLitSupported ⟨natA :: env.consts⟩ = false)
    (hwf : EnvWF ⟨natA :: env.consts⟩) :
    Nonempty (EnvModelM V μ ⟨natA :: env.consts⟩) := by
  refine nonempty_of_exists (declStep_preserves_of_basis_cons_gen mp
    (A := fun _ => AnnotTerm.const .nat []) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT natA.name ψ
          = some (Term.const .nat []) from rfl] at hp
        rw [← Option.some.inj hp]
        rfl)
      (fun _ h => nomatch h) (fun _ _ _ _ h => nomatch h))
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, denoteMeta_natA_type ψ⟩) ?_ ?_ ?_ ?_)
  · intro ψ ta h ρ
    rw [denoteMeta_natA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact WellDenotedV_bconst_type V .nat [] ρ
  · intro ψ ta h ρ
    rw [denoteMeta_natA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact bval_mem_type V .nat [] ρ
  · intro _ _ _ hg
    rw [hguard] at hg
    exact nomatch hg
  · exact fun m₂ hac φ => recRules_cons_fresh mp (c₀ := natA) hfresh
      (fun _ h => nomatch h)
      (fun _ _ _ _ h => nomatch h) m₂ hac φ

/-- **`Nat.zero`, installed at the P tier.** -/
theorem extendNatZero (mp : EnvModelM V μ env)
    (hN : env.find? natName = some natA)
    (hfresh : env.find? natZeroName = none)
    (hguard : ConLeche.natLitSupported ⟨natZeroA :: env.consts⟩ = false)
    (hwf : EnvWF ⟨natZeroA :: env.consts⟩) :
    Nonempty (EnvModelM V μ ⟨natZeroA :: env.consts⟩) := by
  have hty := fun ψ =>
    denoteMeta_natZeroA_type (m := mp.base2)
      (A := fun _ => AnnotTerm.const .natZero []) ψ hN
  refine nonempty_of_exists (declStep_preserves_of_basis_cons_gen mp
    (A := fun _ => AnnotTerm.const .natZero []) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT natZeroA.name ψ
          = some (Term.const .natZero []) from rfl] at hp
        rw [← Option.some.inj hp]
        rfl)
      (fun _ h => nomatch h) (fun _ _ _ _ h => nomatch h))
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_ ?_ ?_)
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact WellDenotedV_bconst_type V .natZero [] ρ
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact bval_mem_type V .natZero [] ρ
  · intro _ _ _ hg
    rw [hguard] at hg
    exact nomatch hg
  · exact fun m₂ hac φ => recRules_cons_fresh mp (c₀ := natZeroA)
      (hntc := fun _ h => nomatch h)
      hfresh (fun _ _ _ _ h => nomatch h) m₂ hac φ

/-- **`Nat.succ`, installed at the P tier** — the cons where the
literal guard becomes true, so `nat_heads` is bespoke here and nowhere
else.  Its content is `natzero_mem` and `natSuccV_mem`. -/
theorem extendNatSucc (mp : EnvModelM V μ env)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hfresh : env.find? natSuccName = none)
    (hwf : EnvWF ⟨natSuccA :: env.consts⟩) :
    Nonempty (EnvModelM V μ ⟨natSuccA :: env.consts⟩) := by
  have hty := fun ψ =>
    denoteMeta_natSuccA_type (m := mp.base2)
      (A := fun _ => AnnotTerm.const .natSucc []) ψ hN
  refine nonempty_of_exists (declStep_preserves_of_basis_cons_gen mp
    (A := fun _ => AnnotTerm.const .natSucc []) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT natSuccA.name ψ
          = some (Term.const .natSucc []) from rfl] at hp
        rw [← Option.some.inj hp]
        rfl)
      (fun _ h => nomatch h) (fun _ _ _ _ h => nomatch h))
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_ ?_ ?_)
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact (bitAgree_wellDenotedV (bitAgree_natSuccA ψ) ρ).mpr
      (WellDenotedV_bconst_type V .natSucc [] ρ)
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [AnnotTerm.BitAgree.interp_eq V (bitAgree_natSuccA ψ) ρ]
    exact bval_mem_type V .natSucc [] ρ
  · -- `nat_heads`, bespoke: the three leaves are the two prefix pins
    -- and the fresh one
    intro m₂ hac φ _ ρ
    have hZl : m₂.acval natZeroName (Level.substFn φ [] [])
        = AnnotTerm.const .natZero [] := by
      rw [hac, acvalWith_ne (by decide)]
      refine acval_basis_pinned (m := mp.base2) hZ (by decide) ?_
      simp +decide [ConLeche.Verify.pinnedStructT]
    have hNl : m₂.acval natName (Level.substFn φ [] [])
        = AnnotTerm.const .nat [] := by
      rw [hac, acvalWith_ne (by decide)]
      refine acval_basis_pinned (m := mp.base2) hN (by decide) ?_
      simp +decide [ConLeche.Verify.pinnedStructT]
    have hSl : m₂.acval natSuccName (Level.substFn φ [] [])
        = AnnotTerm.const .natSucc [] := by
      rw [hac, show natSuccName = natSuccA.name from rfl,
        acvalWith_self]
    rw [hZl, hNl, hSl]
    exact ⟨by simpa [interp_const, bval] using
        (natzero_mem : (natzero : V) ∈ˢ omega),
      by simpa [interp_const, bval] using natSuccV_mem V⟩
  · exact fun m₂ hac φ => recRules_cons_fresh mp (c₀ := natSuccA)
      (hntc := fun _ h => nomatch h)
      hfresh (fun _ _ _ _ h => nomatch h) m₂ hac φ

/-! ### The two firing rules

The three telescope domains, named once: their readings are the
`Interp/Value.lean` spaces up to `piR_zero_agree`, which is the whole
content of "the reading's numerals are the pin's". -/

/-- The motive binder's domain reading. -/
def natMotiveTy (ψ : Name → Nat) : AnnotTerm :=
  .pi 0 (pwBit ψ .never) (.const .nat []) (.sort (ψ uN))

/-- The step binder's domain reading. -/
def natStepTy (ψ : Name → Nat) : AnnotTerm :=
  .pi 0 (pwBit ψ (.ifAllZero [uN])) (.const .nat [])
    (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.app (.bvar 2) (.bvar 0))
      (.app (.bvar 3) (.app (.const .natSucc []) (.bvar 1))))

theorem natMotiveTy_interp (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (natMotiveTy ψ) = natMotiveSpace V (ψ uN) := by
  rw [natMotiveTy, interp_pi, natMotiveSpace]
  refine piR_zero_agree (show pwBit ψ ConLeche.PropWhen.never = 0
      ↔ ψ uN + 1 = 0 by rw [pwBit_never]; simp) (fun _ _ => rfl)

theorem natStepTy_interp (ψ : Name → Nat) (ρ : Nat → V) (M z : V) :
    interp V (cons z (cons M ρ)) (natStepTy ψ)
      = natStepSpace V (pwBit ψ (.ifAllZero [uN])) M := by
  rw [natStepTy, interp_pi, natStepSpace]
  simp only [interp_const, bval]
  refine piR_congr fun n hn => ?_
  rw [interp_pi]
  simp only [interp_app, interp_bvar, interp_const, cons, bval]
  exact piR_congr fun _ _ => by rw [natSuccV_app V hn]

/-- The `zero` rule's RHS reading. -/
def natZeroRa (ψ : Name → Nat) : AnnotTerm :=
  .lam (pwBit ψ (.ifAllZero [uN])) (natMotiveTy ψ)
    (.lam (pwBit ψ (.ifAllZero [uN]))
      (.app (.bvar 0) (.const .natZero []))
      (.lam (pwBit ψ (.ifAllZero [uN])) (natStepTy ψ) (.bvar 1)))

/-- The `succ` rule's RHS reading — the recursive occurrence is the
*fresh* leaf, so it reads to `.const .natRec [ψ u]`. -/
def natSuccRa (ψ : Name → Nat) : AnnotTerm :=
  .lam (pwBit ψ (.ifAllZero [uN])) (natMotiveTy ψ)
    (.lam (pwBit ψ (.ifAllZero [uN]))
      (.app (.bvar 0) (.const .natZero []))
      (.lam (pwBit ψ (.ifAllZero [uN])) (natStepTy ψ)
        (.lam (pwBit ψ (.ifAllZero [uN])) (.const .nat [])
          (.app (.app (.bvar 1) (.bvar 0))
            (.app (.app (.app (.app (.const .natRec [ψ uN]) (.bvar 3))
              (.bvar 2)) (.bvar 1)) (.bvar 0))))))

theorem denoteMeta_natRec_zeroRhs (ψ : Name → Nat)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA) :
    denoteMeta (acvalWith m.acval natRecA.name A)
        ⟨natRecA :: env.consts⟩ ψ 0 natRecZeroRule.rhs
      = some (natZeroRa ψ) := by
  obtain ⟨hNc, hZc, hSc⟩ :=
    denoteMeta_natRec_leaves (m := m) (A := A) ψ hN hZ hS
  rw [show natRecZeroRule.rhs = Expr.lam
      (Expr.forallE (.const natName [])
        (.sort (.param uN)) { pw := .never })
      (Expr.lam
        (.app (.bvar 0) (.const natZeroName []))
        (Expr.lam
          (Expr.forallE (.const natName [])
            (Expr.forallE
              (.app (.bvar 2) (.bvar 0))
              (.app (.bvar 3) (.app (.const natSuccName []) (.bvar 1)))
              { pw := .ifAllZero [uN] })
            { pw := .ifAllZero [uN] })
          (.bvar 1) { pw := .ifAllZero [uN] })
        { pw := .ifAllZero [uN] })
      { pw := .ifAllZero [uN] } from rfl]
  simp [denoteMeta_lam, denoteMeta_forallE, denoteMeta_sort, denoteMeta_app,
    denoteMeta_fvar, Expr.instantiate1, hNc, hZc, hSc, Level.eval,
    natZeroRa, natMotiveTy, natStepTy]

theorem denoteMeta_natRec_succRhs (ψ : Name → Nat)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA) :
    denoteMeta (acvalWith m.acval natRecA.name
        (fun ψ => AnnotTerm.const .natRec [ψ uN]))
        ⟨natRecA :: env.consts⟩ ψ 0 natRecSuccRule.rhs
      = some (natSuccRa ψ) := by
  obtain ⟨hNc, hZc, hSc⟩ :=
    denoteMeta_natRec_leaves (m := m)
      (A := fun ψ => AnnotTerm.const .natRec [ψ uN]) ψ hN hZ hS
  have hRc : ∀ d : Nat,
      denoteMeta (acvalWith m.acval natRecA.name
          (fun ψ => AnnotTerm.const .natRec [ψ uN]))
        ⟨natRecA :: env.consts⟩ ψ d
        (.const (natName.str "rec") [.param uN])
        = some (AnnotTerm.const .natRec [ψ uN]) := by
    intro d
    have hf : (⟨natRecA :: env.consts⟩ : Env).find? (natName.str "rec")
        = some natRecA := by
      rw [ConLeche.Env.find?_cons]; exact if_pos rfl
    rw [denoteMeta_const hf (by rfl),
      show natName.str "rec" = natRecA.name from rfl, acvalWith_self]
    show some (AnnotTerm.const .natRec
      [Level.substFn ψ natRecA.toConstantVal.levelParams
        [Level.param uN] uN]) = _
    rw [show Level.substFn ψ natRecA.toConstantVal.levelParams
        [Level.param uN] uN = ψ uN from rfl]
  rw [show natRecSuccRule.rhs = Expr.lam
      (Expr.forallE (.const natName [])
        (.sort (.param uN)) { pw := .never })
      (Expr.lam
        (.app (.bvar 0) (.const natZeroName []))
        (Expr.lam
          (Expr.forallE (.const natName [])
            (Expr.forallE
              (.app (.bvar 2) (.bvar 0))
              (.app (.bvar 3) (.app (.const natSuccName []) (.bvar 1)))
              { pw := .ifAllZero [uN] })
            { pw := .ifAllZero [uN] })
          (Expr.lam (.const natName [])
            (.app (.app (.bvar 1) (.bvar 0))
              (.app (.app (.app (.app
                (.const (natName.str "rec") [.param uN]) (.bvar 3))
                (.bvar 2)) (.bvar 1)) (.bvar 0)))
            { pw := .ifAllZero [uN] })
          { pw := .ifAllZero [uN] })
        { pw := .ifAllZero [uN] })
      { pw := .ifAllZero [uN] } from rfl]
  simp [denoteMeta_lam, denoteMeta_forallE, denoteMeta_sort, denoteMeta_app,
    denoteMeta_fvar, Expr.instantiate1, hNc, hZc, hSc, hRc, Level.eval,
    natSuccRa, natMotiveTy, natStepTy]

/-- The step space's numeral is read only through its zero test. -/
theorem natStepSpace_bit_agree {b u : Nat} (hz : b = 0 ↔ u = 0)
    (M : V) : natStepSpace V b M = natStepSpace V u M := by
  rw [natStepSpace, natStepSpace]
  exact piR_zero_agree hz fun _ _ => piR_zero_agree hz fun _ _ => rfl

/-- The motive binder's domain is graded — no numeral is read. -/
theorem natMotiveTy_wellDenotedV (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenotedV V ρ (natMotiveTy ψ) :=
  ⟨⟨trivial, fun _ _ => trivial⟩,
    ⟨trivial, fun _ _ => trivial, fun h => by
      rw [pwBit_never] at h; exact nomatch h⟩⟩

/-- The step binder's domain is graded, under a motive membership: the
three residual fibre obligations are `natMotive_apply` at `n`, at
`n + 1`, and `piR_zero_mem_univZero`. -/
theorem natStepTy_wellDenotedV (ψ : Name → Nat) (ρ : Nat → V) (M z : V)
    (hM : M ∈ˢ natMotiveSpace V (ψ uN)) :
    WellDenotedV V (cons z (cons M ρ)) (natStepTy ψ) := by
  have hMn : ∀ n : V, n ∈ˢ (omega : V) → app M n ∈ˢ (univ (ψ uN) : V) :=
    fun n hn => natMotive_apply V hM hn
  have hdom : ∀ n : V,
      interp V (cons n (cons z (cons M ρ))) (.app (.bvar 2) (.bvar 0))
        = app M n := by
    intro n; simp [interp_app, interp_bvar, cons]
  have hcod : ∀ (n ih : V),
      interp V (cons ih (cons n (cons z (cons M ρ))))
          (.app (.bvar 3) (.app (.const .natSucc []) (.bvar 1)))
        = app M (app (natSuccV V) n) := by
    intro n ih; simp [interp_app, interp_bvar, interp_const, cons,
      bval]
  have hM' : M ∈ˢ piR (ψ uN + 1) (omega : V) fun _ => univ (ψ uN) := hM
  constructor
  · refine ⟨trivial, fun n hn => ?_⟩
    have hn' : n ∈ˢ (omega : V) := by
      simpa [interp_const, bval] using hn
    refine ⟨⟨trivial, trivial, ψ uN + 1, omega, fun _ => univ (ψ uN),
        by simpa [interp_bvar, cons] using hM',
        by simpa [interp_bvar, cons] using hn',
        fun h => absurd h (Nat.succ_ne_zero _)⟩,
      fun ih _ => ⟨trivial, ⟨trivial, trivial, 1, omega,
        fun _ => omega, natSuccV_mem V,
        by simpa [interp_bvar, cons] using hn',
        fun h => absurd h Nat.one_ne_zero⟩,
        ψ uN + 1, omega, fun _ => univ (ψ uN),
        by simpa [interp_bvar, cons] using hM',
        by rw [interp_app, interp_const, interp_bvar]
           show app (natSuccV V) _ ∈ˢ _
           rw [show cons ih (cons n (cons z (cons M ρ))) 1 = n from rfl,
             natSuccV_app V hn']
           exact natsucc_mem hn',
        fun h => absurd h (Nat.succ_ne_zero _)⟩⟩
  · refine ⟨trivial, fun n hn => ?_, fun hz n hn => ?_⟩
    · have hn' : n ∈ˢ (omega : V) := by
        simpa [interp_const, bval] using hn
      refine ⟨⟨trivial, trivial⟩,
        fun _ _ => ⟨trivial, ⟨trivial, trivial⟩⟩, fun hz ih _ => ?_⟩
      rw [hcod n ih, natSuccV_app V hn']
      have := hMn (natsucc n) (natsucc_mem hn')
      rw [(pwBit_ifAllZero_single ψ uN).mp hz, univ_zero] at this
      exact this
    · rw [interp_pi]
      rw [hz]
      exact piR_zero_mem_univZero

/-! ### The two RHS towers, interpreted and graded -/

theorem natZeroRa_interp (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (natZeroRa ψ)
      = lamR (pwBit ψ (.ifAllZero [uN])) (natMotiveSpace V (ψ uN))
          (fun M => lamR (pwBit ψ (.ifAllZero [uN])) (app M natzero)
            (fun z => lamR (pwBit ψ (.ifAllZero [uN]))
              (natStepSpace V (pwBit ψ (.ifAllZero [uN])) M)
              (fun _ => z))) := by
  simp only [natZeroRa, interp_lam, interp_app, interp_bvar,
    interp_const, cons, bval, natMotiveTy_interp, natStepTy_interp]

theorem natSuccRa_interp (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (natSuccRa ψ)
      = lamR (pwBit ψ (.ifAllZero [uN])) (natMotiveSpace V (ψ uN))
          (fun M => lamR (pwBit ψ (.ifAllZero [uN])) (app M natzero)
            (fun z => lamR (pwBit ψ (.ifAllZero [uN]))
              (natStepSpace V (pwBit ψ (.ifAllZero [uN])) M)
              (fun s => lamR (pwBit ψ (.ifAllZero [uN])) omega
                (fun n => app (app s n)
                  (app (app (app (app (natRecV V (ψ uN)) M) z) s)
                    n))))) := by
  simp only [natSuccRa, interp_lam, interp_app, interp_bvar,
    interp_const, cons, bval, natMotiveTy_interp,
    natStepTy_interp, ConLeche.Term.lv, List.getD_cons_zero]

/-- **The recursive spine is graded**, once and for all: four
`bconst_app_data` steps at `Nat.rec`'s own `typeAV` binders, with the
four domains identified with `Interp/Value.lean`'s spaces.  Used at
the `succ` rule, where the RHS mentions the recursor. -/
theorem natRecSpine_wellDenoted {u : Nat} (ρ : Nat → V) {e1 e2 e3 e4 : AnnotTerm}
    (h1 : WellDenoted V ρ e1) (h2 : WellDenoted V ρ e2)
    (h3 : WellDenoted V ρ e3) (h4 : WellDenoted V ρ e4)
    (m1 : interp V ρ e1 ∈ˢ natMotiveSpace V u)
    (m2 : interp V ρ e2 ∈ˢ app (interp V ρ e1) natzero)
    (m3 : interp V ρ e3 ∈ˢ natStepSpace V u (interp V ρ e1))
    (m4 : interp V ρ e4 ∈ˢ (omega : V)) :
    WellDenoted V ρ
      (.app (.app (.app (.app (.const .natRec [u]) e1) e2) e3) e4) := by
  have hlv : ConLeche.Term.lv [u] 0 = u := rfl
  have d1 : interp V ρ (arrowA 1 (u + 1) natTyAV (.sort u))
      = natMotiveSpace V u := by
    simp [arrowA, natTyAV, AnnotTerm.lift, AnnotTerm.liftN, interp_pi,
      interp_const, interp_sort, bval, natMotiveSpace]
  have d2 : ∀ a1 : V, interp V (cons a1 ρ)
      (.app (.bvar 0) natZeroAV) = app a1 natzero := by
    intro a1
    simp [natZeroAV, interp_app, interp_bvar, interp_const, cons,
      bval]
  have d3 : ∀ a1 a2 : V, interp V (cons a2 (cons a1 ρ))
      (AnnotTerm.pi 1 u natTyAV (.pi u u (.app (.bvar 2) (.bvar 0))
        (.app (.bvar 3) (natSuccAV (.bvar 1)))))
      = natStepSpace V u a1 := by
    intro a1 a2
    rw [interp_pi, natStepSpace]
    simp only [natTyAV, interp_const, bval]
    refine piR_congr fun k hk => ?_
    rw [interp_pi]
    simp only [natSuccAV, interp_app, interp_bvar, interp_const,
      cons, bval]
    exact piR_congr fun _ _ => by rw [natSuccV_app V hk]
  have d4 : ∀ a1 a2 a3 : V,
      interp V (cons a3 (cons a2 (cons a1 ρ))) natTyAV = (omega : V) := by
    intro _ _ _; simp [natTyAV, interp_const, bval]
  rw [WellDenoted_app]
  refine ⟨?_, h4, ?_⟩
  · rw [WellDenoted_app]
    refine ⟨?_, h3, ?_⟩
    · rw [WellDenoted_app]
      refine ⟨⟨trivial, h1, ?_⟩, h2, ?_⟩
      · exact bconst_app_data V .natRec [u] ρ rfl (by rw [hlv, d1]; exact m1)
      · refine bconst_app_dataAV V .natRec [u] ρ rfl
          (by rw [hlv, d1]; exact m1) ?_
        rw [d2]; exact m2
    · refine bconst_app_data3 V .natRec [u] ρ rfl
        (by rw [hlv, d1]; exact m1) (by rw [d2]; exact m2) ?_
      rw [hlv, d3]; exact m3
  · refine bconst_app_data4 V .natRec [u] ρ rfl
      (by rw [hlv, d1]; exact m1) (by rw [d2]; exact m2)
      (by rw [hlv, d3]; exact m3) ?_
    rw [d4]; exact m4

/-- The spine is bit-valid: `AnnotValid`'s `.app` clause is
structural. -/
theorem natRecSpine_validV {u : Nat} (ρ : Nat → V)
    {e1 e2 e3 e4 : AnnotTerm}
    (h1 : AnnotValid V ρ e1) (h2 : AnnotValid V ρ e2)
    (h3 : AnnotValid V ρ e3) (h4 : AnnotValid V ρ e4) :
    AnnotValid V ρ
      (.app (.app (.app (.app (.const .natRec [u]) e1) e2) e3) e4) :=
  ⟨⟨⟨⟨trivial, h1⟩, h2⟩, h3⟩, h4⟩

/-- The `zero` rule's RHS tower is graded. -/
theorem natZeroRa_wellDenotedV (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenotedV V ρ (natZeroRa ψ) := by
  have hb : ∀ M : V, M ∈ˢ natMotiveSpace V (ψ uN) →
      pwBit ψ (ConLeche.PropWhen.ifAllZero [uN]) = 0 →
      app M natzero ∈ˢ (univZero : V) := by
    intro M hM hz
    have hh := natMotive_apply V hM (natzero_mem (V := V))
    rw [(pwBit_ifAllZero_single ψ uN).mp hz, univ_zero] at hh
    exact hh
  have hzty : ∀ M : V, interp V (cons M ρ)
      (AnnotTerm.app (.bvar 0) (.const .natZero [])) = app M natzero := by
    intro M; simp [interp_app, interp_bvar, interp_const, cons, bval]
  constructor
  · rw [natZeroRa, WellDenoted_lam, natMotiveTy_interp]
    refine ⟨(natMotiveTy_wellDenotedV ψ ρ).1, fun M hM => ?_, ?_⟩
    · have hM' : M ∈ˢ piR (ψ uN + 1) (omega : V)
          fun _ => univ (ψ uN) := hM
      rw [WellDenoted_lam, hzty]
      refine ⟨⟨trivial, trivial, ψ uN + 1, omega, fun _ => univ (ψ uN),
          by simpa [interp_bvar, cons] using hM',
          by simpa [interp_const, bval]
            using (natzero_mem : (natzero : V) ∈ˢ omega),
          fun h => absurd h (Nat.succ_ne_zero _)⟩,
        fun z hz => ?_, ?_⟩
      · rw [WellDenoted_lam, natStepTy_interp]
        exact ⟨(natStepTy_wellDenotedV ψ ρ M z hM).1, fun _ _ => trivial,
          fun _ => app M natzero,
          fun _ _ => by simpa [interp_bvar, cons] using hz,
          fun h _ _ => hb M hM h⟩
      · refine ⟨fun _ => piR (pwBit ψ (.ifAllZero [uN]))
            (natStepSpace V (pwBit ψ (.ifAllZero [uN])) M)
            (fun _ => app M natzero),
          fun z hz => ?_,
          fun h _ _ => by rw [h]; exact piR_zero_mem_univZero⟩
        rw [interp_lam, natStepTy_interp]
        exact lamR_mem fun _ _ => by simpa [interp_bvar, cons] using hz
    · refine ⟨fun M => piR (pwBit ψ (.ifAllZero [uN])) (app M natzero)
          (fun _ => piR (pwBit ψ (.ifAllZero [uN]))
            (natStepSpace V (pwBit ψ (.ifAllZero [uN])) M)
            (fun _ => app M natzero)),
        fun M hM => ?_,
        fun h _ _ => by rw [h]; exact piR_zero_mem_univZero⟩
      rw [interp_lam, hzty]
      refine lamR_mem fun z hz => ?_
      rw [interp_lam, natStepTy_interp]
      exact lamR_mem fun _ _ => by simpa [interp_bvar, cons] using hz
  · rw [natZeroRa, AnnotValid_lam, natMotiveTy_interp]
    refine ⟨(natMotiveTy_wellDenotedV ψ ρ).2, fun M hM => ?_⟩
    rw [AnnotValid_lam, hzty]
    exact ⟨⟨trivial, trivial⟩, fun z hz =>
      ⟨(natStepTy_wellDenotedV ψ ρ M z hM).2, fun _ _ => trivial⟩⟩

set_option maxHeartbeats 1000000 in
/-- The `succ` rule's RHS tower is graded — the extra layer over the
`zero` rule's is the recursive spine, `natRecSpine_wellDenoted`. -/
theorem natSuccRa_wellDenotedV (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenotedV V ρ (natSuccRa ψ) := by
  have hzty : ∀ M : V, interp V (cons M ρ)
      (AnnotTerm.app (.bvar 0) (.const .natZero [])) = app M natzero := by
    intro M; simp [interp_app, interp_bvar, interp_const, cons, bval]
  have hfib : ∀ M : V, M ∈ˢ natMotiveSpace V (ψ uN) → ∀ n : V,
      n ∈ˢ (omega : V) →
      pwBit ψ (ConLeche.PropWhen.ifAllZero [uN]) = 0 →
      app M n ∈ˢ (univZero : V) := by
    intro M hM n hn hz
    have hh := natMotive_apply V hM hn
    rw [(pwBit_ifAllZero_single ψ uN).mp hz, univ_zero] at hh
    exact hh
  -- the fourth λ's body, at a fixed motive/minor/step
  have body : ∀ (M z s : V), M ∈ˢ natMotiveSpace V (ψ uN) →
      z ∈ˢ app M natzero →
      s ∈ˢ natStepSpace V (pwBit ψ (.ifAllZero [uN])) M →
      ∀ n : V, n ∈ˢ (omega : V) →
      WellDenoted V (cons n (cons s (cons z (cons M ρ))))
          (.app (.app (.bvar 1) (.bvar 0))
            (.app (.app (.app (.app (.const .natRec [ψ uN]) (.bvar 3))
              (.bvar 2)) (.bvar 1)) (.bvar 0))) ∧
        interp V (cons n (cons s (cons z (cons M ρ))))
            (.app (.app (.bvar 1) (.bvar 0))
              (.app (.app (.app (.app (.const .natRec [ψ uN]) (.bvar 3))
                (.bvar 2)) (.bvar 1)) (.bvar 0)))
          ∈ˢ app M (natsucc n) := by
    intro M z s hM hz hs n hn
    have hs' : s ∈ˢ natStepSpace V (ψ uN) M := by
      rwa [natStepSpace_bit_agree (pwBit_ifAllZero_single ψ uN)] at hs
    have hs'' : s ∈ˢ piR (ψ uN) (omega : V)
        fun k => piR (ψ uN) (app M k) fun _ => app M (natsucc k) := hs'
    have hsn : app s n ∈ˢ piR (ψ uN) (app M n)
        (fun _ => app M (natsucc n)) :=
      app_mem_piR (B := fun k => piR (ψ uN) (app M k)
        (fun _ => app M (natsucc k))) hs'' hn
        (fun h k hk => by rw [h]; exact piR_zero_mem_univZero)
    have hrec : app (app (app (app (natRecV V (ψ uN)) M) z) s) n
        ∈ˢ app M n := by
      rw [natRecV_app V hM hz hs' hn]
      exact natRecV_mem_fibre V hM hz hs' hn
    have espine : interp V (cons n (cons s (cons z (cons M ρ))))
        (.app (.app (.app (.app (.const .natRec [ψ uN]) (.bvar 3))
          (.bvar 2)) (.bvar 1)) (.bvar 0))
        = app (app (app (app (natRecV V (ψ uN)) M) z) s) n := by
      simp [interp_app, interp_bvar, interp_const, cons, bval,
        ConLeche.Term.lv]
    have eapp : interp V (cons n (cons s (cons z (cons M ρ))))
        (AnnotTerm.app (.bvar 1) (.bvar 0)) = app s n := by
      simp [interp_app, interp_bvar, cons]
    refine ⟨?_, ?_⟩
    · rw [WellDenoted_app]
      refine ⟨⟨trivial, trivial, ψ uN, omega,
          fun k => piR (ψ uN) (app M k) (fun _ => app M (natsucc k)),
          by simpa [interp_bvar, cons] using hs'',
          by simpa [interp_bvar, cons] using hn,
          fun h k hk => by rw [h]; exact piR_zero_mem_univZero⟩,
        ?_, ?_⟩
      · refine natRecSpine_wellDenoted (u := ψ uN) _ trivial trivial trivial
          trivial ?_ ?_ ?_ ?_
        · simpa [interp_bvar, cons] using hM
        · simpa [interp_bvar, cons] using hz
        · simpa [interp_bvar, cons] using hs'
        · simpa [interp_bvar, cons] using hn
      · exact ⟨ψ uN, app M n, fun _ => app M (natsucc n),
          by rw [eapp]; exact hsn,
          by rw [espine]; exact hrec,
          fun h k hk => by
            have hh := natMotive_apply V hM (natsucc_mem hn)
            rw [h, univ_zero] at hh
            exact hh⟩
    · rw [interp_app, eapp, espine]
      exact app_mem_piR hsn hrec (fun h k hk => by
        have hh := natMotive_apply V hM (natsucc_mem hn)
        rw [h, univ_zero] at hh
        exact hh)
  constructor
  · rw [natSuccRa, WellDenoted_lam, natMotiveTy_interp]
    refine ⟨(natMotiveTy_wellDenotedV ψ ρ).1, fun M hM => ?_, ?_⟩
    · have hM' : M ∈ˢ piR (ψ uN + 1) (omega : V)
          fun _ => univ (ψ uN) := hM
      rw [WellDenoted_lam, hzty]
      refine ⟨⟨trivial, trivial, ψ uN + 1, omega, fun _ => univ (ψ uN),
          by simpa [interp_bvar, cons] using hM',
          by simpa [interp_const, bval]
            using (natzero_mem : (natzero : V) ∈ˢ omega),
          fun h => absurd h (Nat.succ_ne_zero _)⟩,
        fun z hz => ?_, ?_⟩
      · rw [WellDenoted_lam, natStepTy_interp]
        refine ⟨(natStepTy_wellDenotedV ψ ρ M z hM).1, fun s hs => ?_, ?_⟩
        · rw [WellDenoted_lam]
          simp only [interp_const, bval]
          exact ⟨trivial, fun n hn => (body M z s hM hz hs n hn).1,
            fun n => app M (natsucc n),
            fun n hn => (body M z s hM hz hs n hn).2,
            fun h n hn => hfib M hM (natsucc n) (natsucc_mem hn) h⟩
        · refine ⟨fun _ => piR (pwBit ψ (.ifAllZero [uN])) omega
              (fun n => app M (natsucc n)),
            fun s hs => ?_,
            fun h _ _ => by rw [h]; exact piR_zero_mem_univZero⟩
          rw [interp_lam]
          simp only [interp_const, bval]
          exact lamR_mem fun n hn => (body M z s hM hz hs n hn).2
      · refine ⟨fun _ => piR (pwBit ψ (.ifAllZero [uN]))
            (natStepSpace V (pwBit ψ (.ifAllZero [uN])) M)
            (fun _ => piR (pwBit ψ (.ifAllZero [uN])) omega
              (fun n => app M (natsucc n))),
          fun z hz => ?_,
          fun h _ _ => by rw [h]; exact piR_zero_mem_univZero⟩
        rw [interp_lam, natStepTy_interp]
        refine lamR_mem fun s hs => ?_
        rw [interp_lam]
        simp only [interp_const, bval]
        exact lamR_mem fun n hn => (body M z s hM hz hs n hn).2
    · refine ⟨fun M => piR (pwBit ψ (.ifAllZero [uN])) (app M natzero)
          (fun _ => piR (pwBit ψ (.ifAllZero [uN]))
            (natStepSpace V (pwBit ψ (.ifAllZero [uN])) M)
            (fun _ => piR (pwBit ψ (.ifAllZero [uN])) omega
              (fun n => app M (natsucc n)))),
        fun M hM => ?_,
        fun h _ _ => by rw [h]; exact piR_zero_mem_univZero⟩
      rw [interp_lam, hzty]
      refine lamR_mem fun z hz => ?_
      rw [interp_lam, natStepTy_interp]
      refine lamR_mem fun s hs => ?_
      rw [interp_lam]
      simp only [interp_const, bval]
      exact lamR_mem fun n hn => (body M z s hM hz hs n hn).2
  · rw [natSuccRa, AnnotValid_lam, natMotiveTy_interp]
    refine ⟨(natMotiveTy_wellDenotedV ψ ρ).2, fun M hM => ?_⟩
    rw [AnnotValid_lam, hzty]
    refine ⟨⟨trivial, trivial⟩, fun z hz => ?_⟩
    rw [AnnotValid_lam, natStepTy_interp]
    refine ⟨(natStepTy_wellDenotedV ψ ρ M z hM).2, fun s hs => ?_⟩
    rw [AnnotValid_lam]
    exact ⟨trivial, fun n hn =>
      ⟨⟨trivial, trivial⟩, natRecSpine_validV _ trivial trivial trivial
        trivial⟩⟩

/-! ### The two rows

Both rules are `.plain` (ENDGAME F §3), so the `.nested` conjuncts are
`nomatch` at both.  What differs from `PUnit.rec` is the shape of the
fired equality — `natrec_zero` at one rule, `natrec_succ` at the other
— and that the `succ` rule's right-hand side mentions the recursor
itself, read through the **fresh** leaf. -/

/-- The recursor's telescope, unpacked into the four memberships
`Interp/Value.lean`'s laws are stated with. -/
theorem natRecTelescope (ψ : Name → Nat) (ρ : Nat → V)
    {xs : List AnnotTerm} (hxs : xs.length = 3) (tl rest : AnnotTerm)
    (hfit : TeleFitPA V ρ
      (.pi 0 (pwBit ψ (.ifAllZero [uN])) (natMotiveTy ψ)
        (.pi 0 (pwBit ψ (.ifAllZero [uN]))
          (.app (.bvar 0) (.const .natZero []))
          (.pi 0 (pwBit ψ (.ifAllZero [uN])) (natStepTy ψ)
            (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.const .nat [])
              (.app (.bvar 3) (.bvar 0))))))
      (xs ++ [tl]) rest) :
    ∃ M z s : AnnotTerm, xs = [M, z, s] ∧
      interp V ρ M ∈ˢ natMotiveSpace V (ψ uN) ∧
      interp V ρ z ∈ˢ app (interp V ρ M) natzero ∧
      interp V ρ s ∈ˢ natStepSpace V (ψ uN) (interp V ρ M) ∧
      interp V ρ tl ∈ˢ (omega : V) := by
  obtain ⟨M, z, s, rfl⟩ : ∃ a b c, xs = [a, b, c] := by
    match xs, hxs with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  cases hfit with | cons h1 hfit =>
  cases hfit with | cons h2 hfit =>
  cases hfit with | cons h3 hfit =>
  cases hfit with | cons h4 _ =>
  rw [natMotiveTy_interp] at h1
  refine ⟨M, z, s, rfl, h1, ?_, ?_, ?_⟩
  · simpa [AnnotTerm.inst, AnnotTerm.liftN_zero, interp_app, interp_bvar,
      interp_const, cons, bval] using h2
  · have h3' : interp V ρ s
        ∈ˢ natStepSpace V (pwBit ψ (.ifAllZero [uN])) (interp V ρ M) := by
      have heq : (piR (pwBit ψ (.ifAllZero [uN])) (omega : V) fun x =>
            piR (pwBit ψ (.ifAllZero [uN])) (app (interp V ρ M) x)
              fun _ => app (interp V ρ M) (app (natSuccV V) x))
          = piR (pwBit ψ (.ifAllZero [uN])) omega fun n =>
            piR (pwBit ψ (.ifAllZero [uN])) (app (interp V ρ M) n)
              fun _ => app (interp V ρ M) (natsucc n) :=
        piR_congr fun n hn =>
          piR_congr fun _ _ => by rw [natSuccV_app V hn]
      rw [natStepSpace, ← heq]
      simpa [AnnotTerm.inst, AnnotTerm.liftN_zero, natStepTy,
        interp_liftN2_inst1, interp_liftN3_inst2, interp_pi,
        interp_app, interp_bvar, interp_const, cons_zero, cons_succ,
        bval] using h3
    rwa [natStepSpace_bit_agree (pwBit_ifAllZero_single ψ uN)] at h3'
  · simpa [AnnotTerm.inst, AnnotTerm.liftN_zero, interp_const, bval]
      using h4

/-- The `zero` tower's product membership. -/
theorem natZeroRa_mem (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (natZeroRa ψ)
      ∈ˢ piR (pwBit ψ (.ifAllZero [uN])) (natMotiveSpace V (ψ uN))
        (fun M => piR (pwBit ψ (.ifAllZero [uN])) (app M natzero)
          (fun _ => piR (pwBit ψ (.ifAllZero [uN]))
            (natStepSpace V (pwBit ψ (.ifAllZero [uN])) M)
            (fun _ => app M natzero))) := by
  rw [natZeroRa_interp]
  exact lamR_mem fun _ _ => lamR_mem fun z hz => lamR_mem fun _ _ => hz

/-- The `succ` tower's product membership. -/
theorem natSuccRa_mem (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (natSuccRa ψ)
      ∈ˢ piR (pwBit ψ (.ifAllZero [uN])) (natMotiveSpace V (ψ uN))
        (fun M => piR (pwBit ψ (.ifAllZero [uN])) (app M natzero)
          (fun _ => piR (pwBit ψ (.ifAllZero [uN]))
            (natStepSpace V (pwBit ψ (.ifAllZero [uN])) M)
            (fun _ => piR (pwBit ψ (.ifAllZero [uN])) omega
              (fun n => app M (natsucc n))))) := by
  rw [natSuccRa_interp]
  refine lamR_mem fun M hM => lamR_mem fun z hz =>
    lamR_mem fun s hs => lamR_mem fun n hn => ?_
  have hs' : s ∈ˢ natStepSpace V (ψ uN) M := by
    rwa [natStepSpace_bit_agree (pwBit_ifAllZero_single ψ uN)] at hs
  have hs'' : s ∈ˢ piR (ψ uN) (omega : V)
      fun k => piR (ψ uN) (app M k) fun _ => app M (natsucc k) := hs'
  have hsn := app_mem_piR (B := fun k => piR (ψ uN) (app M k)
      (fun _ => app M (natsucc k))) hs'' hn
    (fun h k hk => by rw [h]; exact piR_zero_mem_univZero)
  refine app_mem_piR hsn ?_ (fun h k hk => by
    have hh := natMotive_apply V hM (natsucc_mem hn)
    rw [h, univ_zero] at hh
    exact hh)
  rw [natRecV_app V hM hz hs' hn]
  exact natRecV_mem_fibre V hM hz hs' hn

/-- The `zero` rule's transport: three `WellDenoted_app` steps over
`natZeroRa_mem`. -/
theorem natZeroRa_transport (ψ : Name → Nat) (ρ : Nat → V)
    {M z s : AnnotTerm}
    (hM : interp V ρ M ∈ˢ natMotiveSpace V (ψ uN))
    (hz : interp V ρ z ∈ˢ app (interp V ρ M) natzero)
    (hs : interp V ρ s
      ∈ˢ natStepSpace V (ψ uN) (interp V ρ M))
    (okM : WellDenotedV V ρ M) (okz : WellDenotedV V ρ z)
    (oks : WellDenotedV V ρ s) :
    WellDenotedV V ρ (.app (.app (.app (natZeroRa ψ) M) z) s) := by
  have hs' : interp V ρ s
      ∈ˢ natStepSpace V (pwBit ψ (.ifAllZero [uN]))
        (interp V ρ M) := by
    rwa [natStepSpace_bit_agree (pwBit_ifAllZero_single ψ uN)]
  have hzero : ∀ K : V, K ∈ˢ natMotiveSpace V (ψ uN) →
      pwBit ψ (ConLeche.PropWhen.ifAllZero [uN]) = 0 →
      app K natzero ∈ˢ (univZero : V) := by
    intro K hK h
    have hh := natMotive_apply V hK (natzero_mem (V := V))
    rw [(pwBit_ifAllZero_single ψ uN).mp h, univ_zero] at hh
    exact hh
  have h1 := app_mem_piR (natZeroRa_mem ψ ρ) hM
    (fun h _ _ => by rw [h]; exact piR_zero_mem_univZero)
  have h2 := app_mem_piR h1 hz
    (fun h _ _ => by rw [h]; exact piR_zero_mem_univZero)
  refine ⟨?_, ?_⟩
  · rw [WellDenoted_app]
    refine ⟨?_, oks.1, _, _, _, h2, hs', fun h _ _ =>
      hzero _ hM h⟩
    rw [WellDenoted_app]
    refine ⟨?_, okz.1, _, _, _, h1, hz, fun h _ _ => by
      rw [h]; exact piR_zero_mem_univZero⟩
    rw [WellDenoted_app]
    exact ⟨(natZeroRa_wellDenotedV ψ ρ).1, okM.1, _, _, _,
      natZeroRa_mem ψ ρ, hM,
      fun h _ _ => by rw [h]; exact piR_zero_mem_univZero⟩
  · exact ⟨⟨⟨(natZeroRa_wellDenotedV ψ ρ).2, okM.2⟩, okz.2⟩, oks.2⟩

/-- The `succ` rule's transport: four steps. -/
theorem natSuccRa_transport (ψ : Name → Nat) (ρ : Nat → V)
    {M z s n : AnnotTerm}
    (hM : interp V ρ M ∈ˢ natMotiveSpace V (ψ uN))
    (hz : interp V ρ z ∈ˢ app (interp V ρ M) natzero)
    (hs : interp V ρ s
      ∈ˢ natStepSpace V (ψ uN) (interp V ρ M))
    (hn : interp V ρ n ∈ˢ (omega : V))
    (okM : WellDenotedV V ρ M) (okz : WellDenotedV V ρ z)
    (oks : WellDenotedV V ρ s) (okn : WellDenotedV V ρ n) :
    WellDenotedV V ρ (.app (.app (.app (.app (natSuccRa ψ) M) z) s) n) := by
  have hs' : interp V ρ s
      ∈ˢ natStepSpace V (pwBit ψ (.ifAllZero [uN]))
        (interp V ρ M) := by
    rwa [natStepSpace_bit_agree (pwBit_ifAllZero_single ψ uN)]
  have h1 := app_mem_piR (natSuccRa_mem ψ ρ) hM
    (fun h _ _ => by rw [h]; exact piR_zero_mem_univZero)
  have h2 := app_mem_piR h1 hz
    (fun h _ _ => by rw [h]; exact piR_zero_mem_univZero)
  have h3 := app_mem_piR h2 hs'
    (fun h _ _ => by rw [h]; exact piR_zero_mem_univZero)
  refine ⟨?_, ?_⟩
  · rw [WellDenoted_app]
    refine ⟨?_, okn.1, _, _, _, h3, hn, fun h k hk => ?_⟩
    · rw [WellDenoted_app]
      refine ⟨?_, oks.1, _, _, _, h2, hs', fun h _ _ => by
        rw [h]; exact piR_zero_mem_univZero⟩
      rw [WellDenoted_app]
      refine ⟨?_, okz.1, _, _, _, h1, hz, fun h _ _ => by
        rw [h]; exact piR_zero_mem_univZero⟩
      rw [WellDenoted_app]
      exact ⟨(natSuccRa_wellDenotedV ψ ρ).1, okM.1, _, _, _,
        natSuccRa_mem ψ ρ, hM,
        fun h _ _ => by rw [h]; exact piR_zero_mem_univZero⟩
    · have hh := natMotive_apply V hM (natsucc_mem hk)
      rw [(pwBit_ifAllZero_single ψ uN).mp h, univ_zero] at hh
      exact hh
  · exact ⟨⟨⟨⟨(natSuccRa_wellDenotedV ψ ρ).2, okM.2⟩, okz.2⟩, oks.2⟩, okn.2⟩

/-- Both rows share this: the recursor's instantiated type reading,
folded back into the two named domains. -/
theorem natRecTyRead (m₂ : EnvModel V ⟨natRecA :: env.consts⟩)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA)
    (hac : m₂.acval = acvalWith m.acval natRecA.name A)
    (φ : Name → Nat) (us : List Level) {ψ : Name → Nat}
    (hψ : ψ = Level.substFn φ natRecA.toConstantVal.levelParams us) :
    denoteMeta m₂.acval ⟨natRecA :: env.consts⟩ φ 0
        (natRecA.toConstantVal.type.instantiateLevelParams
          natRecA.toConstantVal.levelParams us)
      = some (.pi 0 (pwBit ψ (.ifAllZero [uN])) (natMotiveTy ψ)
          (.pi 0 (pwBit ψ (.ifAllZero [uN]))
            (.app (.bvar 0) (.const .natZero []))
            (.pi 0 (pwBit ψ (.ifAllZero [uN])) (natStepTy ψ)
              (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.const .nat [])
                (.app (.bvar 3) (.bvar 0)))))) := by
  rw [denoteMeta_instLevels (acvalParamsAt_of_core m₂) φ, hac,
    denoteMeta_natRecA_type (m := m) _ hN hZ hS, ← hψ]
  rfl

/-- **`Nat.rec`'s `zero` row.** -/
theorem natRecZeroLaw {m : EnvModel V env}
    (m₂ : EnvModel V ⟨natRecA :: env.consts⟩)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA)
    (hac : m₂.acval = acvalWith m.acval natRecA.name
      (fun ψ => AnnotTerm.const .natRec [ψ uN]))
    (φ : Name → Nat) :
    RecRuleLaw m₂ φ natRecA.name natRecA.toConstantVal 3 3
      natRecZeroRule := by
  refine ⟨Nat.le_refl 3, fun us hus => ?_⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Name → Nat,
      ψ = Level.substFn φ natRecA.toConstantVal.levelParams us :=
    ⟨_, rfl⟩
  refine ⟨natZeroRa ψ, ?_, natZeroRa_wellDenotedV ψ, ?_, ?_⟩
  · rw [denoteMeta_instLevels (acvalParamsAt_of_core m₂) φ, hac, hψ,
      denoteMeta_natRec_zeroRhs (m := m) _ hN hZ hS]
  · intro _ _ h; exact nomatch h
  intro cvj cnP cnF hfj usj ρ xs ys TVa TVja restR restC hxs hys husj
    hlev _ hnested hpin hTVa hTVja hfitR hfitC
  obtain rfl : ys = [] := List.eq_nil_of_length_eq_zero hys
  obtain rfl : TVa = _ := (Option.some.inj
    ((natRecTyRead (m := m) m₂ hN hZ hS hac φ us hψ).symm.trans
      hTVa)).symm
  obtain ⟨M, z, s, rfl, hM, hz, hs, -⟩ :=
    natRecTelescope ψ ρ hxs _ restR hfitR
  have hctorL : m₂.acval (RecRule.ctor natRecZeroRule)
      (Level.substFn φ cvj.levelParams usj)
      = AnnotTerm.const .natZero [] := by
    rw [show RecRule.ctor natRecZeroRule = natZeroName from rfl, hac,
      acvalWith_ne (by decide)]
    refine acval_basis_pinned (m := m) hZ (by decide) ?_
    simp +decide [ConLeche.Verify.pinnedStructT]
  have hrecL : m₂.acval natRecA.name
      (Level.substFn φ natRecA.toConstantVal.levelParams us)
      = AnnotTerm.const .natRec [ψ uN] := by
    rw [hac, acvalWith_self, hψ]
  refine ⟨?_, ?_⟩
  · simp only [show natRecZeroRule.ctorParams = 0 from rfl,
      List.take, List.drop, List.cons_append, List.nil_append,
      List.append_nil, AnnotTerm.mkAppN_cons, AnnotTerm.mkAppN_nil, hrecL,
      hctorL, interp_app, interp_const, bval, ConLeche.Term.lv,
      List.getD_cons_zero]
    rw [natRecV_app V hM hz hs (natzero_mem (V := V)), natrec_zero,
      natZeroRa_interp]
    by_cases hbz : pwBit ψ (ConLeche.PropWhen.ifAllZero [uN]) = 0
    · rw [hbz, lamR_zero, app_pt, app_pt, app_pt]
      have hh := natMotive_apply V hM (natzero_mem (V := V))
      rw [(pwBit_ifAllZero_single ψ uN).mp hbz] at hh
      exact mem_univ_zero hh hz
    · rw [app_lamR_pos hbz hM, app_lamR_pos hbz hz,
        app_lamR_pos hbz (by
          rwa [← natStepSpace_bit_agree
            (pwBit_ifAllZero_single ψ uN)] at hs)]
  · intro hxsA _
    simp only [List.take]
    exact natZeroRa_transport ψ ρ hM hz hs
      (hxsA M (by simp)) (hxsA z (by simp)) (hxsA s (by simp))

/-- **`Nat.rec`'s `succ` row** — the RHS mentions the recursor, read
through the *fresh* leaf. -/
theorem natRecSuccLaw {m : EnvModel V env}
    (m₂ : EnvModel V ⟨natRecA :: env.consts⟩)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA)
    (hac : m₂.acval = acvalWith m.acval natRecA.name
      (fun ψ => AnnotTerm.const .natRec [ψ uN]))
    (φ : Name → Nat) :
    RecRuleLaw m₂ φ natRecA.name natRecA.toConstantVal 3 3
      natRecSuccRule := by
  refine ⟨Nat.le_refl 3, fun us hus => ?_⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Name → Nat,
      ψ = Level.substFn φ natRecA.toConstantVal.levelParams us :=
    ⟨_, rfl⟩
  refine ⟨natSuccRa ψ, ?_, natSuccRa_wellDenotedV ψ, ?_, ?_⟩
  · rw [denoteMeta_instLevels (acvalParamsAt_of_core m₂) φ, hac, hψ,
      denoteMeta_natRec_succRhs (m := m) _ hN hZ hS]
  · intro _ _ h; exact nomatch h
  intro cvj cnP cnF hfj usj ρ xs ys TVa TVja restR restC hxs hys husj
    hlev _ hnested hpin hTVa hTVja hfitR hfitC
  obtain ⟨n, rfl⟩ : ∃ a, ys = [a] := by
    match ys, hys with
    | [a], _ => exact ⟨a, rfl⟩
  obtain rfl : TVa = _ := (Option.some.inj
    ((natRecTyRead (m := m) m₂ hN hZ hS hac φ us hψ).symm.trans
      hTVa)).symm
  obtain ⟨M, z, s, rfl, hM, hz, hs, -⟩ :=
    natRecTelescope ψ ρ hxs _ restR hfitR
  have hctorL : m₂.acval (RecRule.ctor natRecSuccRule)
      (Level.substFn φ cvj.levelParams usj)
      = AnnotTerm.const .natSucc [] := by
    rw [show RecRule.ctor natRecSuccRule = natSuccName from rfl, hac,
      acvalWith_ne (by decide)]
    refine acval_basis_pinned (m := m) hS (by decide) ?_
    simp +decide [ConLeche.Verify.pinnedStructT]
  have hrecL : m₂.acval natRecA.name
      (Level.substFn φ natRecA.toConstantVal.levelParams us)
      = AnnotTerm.const .natRec [ψ uN] := by
    rw [hac, acvalWith_self, hψ]
  -- `n`'s membership comes from the *constructor's* telescope
  have hcvj : cvj = natSuccA.toConstantVal := by
    have hS' : (⟨natRecA :: env.consts⟩ : Env).find? natSuccName
        = some natSuccA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hS
    rw [show RecRule.ctor natRecSuccRule = natSuccName from rfl,
      hS'] at hfj
    injection Option.some.inj hfj with a1 _ _
    exact a1.symm
  subst hcvj
  have hTVja' : TVja = .pi 0 (pwBit
      (Level.substFn φ natSuccA.toConstantVal.levelParams usj) .never)
      (.const .nat []) (.const .nat []) := by
    rw [denoteMeta_instLevels (acvalParamsAt_of_core m₂) φ, hac,
      denoteMeta_natSuccTy (m := m) _ (by decide) hN] at hTVja
    exact (Option.some.inj hTVja).symm
  subst hTVja'
  cases hfitC with | cons hn _ =>
  have hn' : interp V ρ n ∈ˢ (omega : V) := by
    simpa [interp_const, bval] using hn
  have hs' : interp V ρ s ∈ˢ natStepSpace V (ψ uN) (interp V ρ M) :=
    hs
  refine ⟨?_, ?_⟩
  · simp only [List.take, List.drop, List.cons_append, List.nil_append,
      AnnotTerm.mkAppN_cons, AnnotTerm.mkAppN_nil, hrecL,
      hctorL, interp_app, interp_const, bval, ConLeche.Term.lv,
      List.getD_cons_zero, show natRecSuccRule.ctorParams = 0 from rfl]
    rw [natSuccV_app V hn',
      natRecV_app V hM hz hs' (natsucc_mem hn'), natrec_succ _ _ hn',
      natSuccRa_interp]
    by_cases hbz : pwBit ψ (ConLeche.PropWhen.ifAllZero [uN]) = 0
    · rw [hbz, lamR_zero, app_pt, app_pt, app_pt, app_pt]
      have hh := natMotive_apply V hM (natsucc_mem hn')
      rw [(pwBit_ifAllZero_single ψ uN).mp hbz] at hh
      have hmem : app (app (interp V ρ s) (interp V ρ n))
          (natrec (interp V ρ z) (interp V ρ s) (interp V ρ n))
          ∈ˢ app (interp V ρ M) (natsucc (interp V ρ n)) := by
        have hsn := app_mem_piR (B := fun k =>
            piR (ψ uN) (app (interp V ρ M) k)
              (fun _ => app (interp V ρ M) (natsucc k)))
          hs' hn' (fun h k hk => by rw [h]; exact piR_zero_mem_univZero)
        exact app_mem_piR hsn
          (natRecV_mem_fibre V hM hz hs' hn')
          (fun h k hk => by
            have h2 := natMotive_apply V hM (natsucc_mem hn')
            rw [h, univ_zero] at h2
            exact h2)
      exact mem_univ_zero hh hmem
    · rw [app_lamR_pos hbz hM, app_lamR_pos hbz hz,
        app_lamR_pos hbz (by
          rwa [← natStepSpace_bit_agree
            (pwBit_ifAllZero_single ψ uN)] at hs'),
        app_lamR_pos hbz hn',
        natRecV_app V hM hz hs' hn']
  · intro hxsA hysA
    simp only [List.take, List.drop,
      show natRecSuccRule.ctorParams = 0 from rfl]
    exact natSuccRa_transport ψ ρ hM hz hs' hn'
      (hxsA M (by simp)) (hxsA z (by simp)) (hxsA s (by simp))
      (hysA n (by simp))

/-- **`Nat.rec`, installed at the P tier.** -/
theorem extendNatRec (mp : EnvModelM V μ env)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA)
    (hfresh : env.find? natRecA.name = none)
    (hwf : EnvWF ⟨natRecA :: env.consts⟩) :
    Nonempty (EnvModelM V μ ⟨natRecA :: env.consts⟩) := by
  have hty := fun ψ =>
    denoteMeta_natRecA_type (m := mp.base2)
      (A := fun ψ => AnnotTerm.const .natRec [ψ uN]) ψ hN hZ hS
  refine nonempty_of_exists (declStep_preserves_of_basis_rec_cons mp
    (A := fun ψ => AnnotTerm.const .natRec [ψ uN]) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT natRecA.name ψ
          = some (Term.const .natRec [ψ uN]) from rfl] at hp
        rw [← Option.some.inj hp]
        rfl)
      (fun _ h => nomatch h)
      (fun _ _ _ _ heq r hr => by
        injection heq with _ _ _ h4
        rw [← h4] at hr
        rcases List.mem_cons.mp hr with rfl | hr'
        · exact ⟨⟨_, _, _, hZ⟩, fun hb => Bool.noConfusion hb,
            fun hb => Bool.noConfusion hb⟩
        rcases List.mem_cons.mp hr' with rfl | hr''
        · exact ⟨⟨_, _, _, hS⟩, fun hb => Bool.noConfusion hb,
            fun hb => Bool.noConfusion hb⟩
        · exact nomatch hr''))
    (fun _ _ => rfl) ?_
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_ ?_)
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact (bitAgree_wellDenotedV (bitAgree_natRecA ψ) ρ).mpr
      (WellDenotedV_bconst_type V .natRec [ψ uN] ρ)
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [AnnotTerm.BitAgree.interp_eq V (bitAgree_natRecA ψ) ρ]
    exact bval_mem_type V .natRec [ψ uN] ρ
  · intro m₂ hac φ
    refine recRules_cons_rec mp hfresh natRecA_eq m₂ hac φ ?_
    intro rl hrl _
    rcases List.mem_cons.mp hrl with rfl | hr'
    · exact natRecZeroLaw (m := mp.base2) m₂ hN hZ hS hac φ
    · rcases List.mem_cons.mp hr' with rfl | hr''
      · exact natRecSuccLaw (m := mp.base2) m₂ hN hZ hS hac φ
      · exact nomatch hr''

/-- **The `Nat` block, installed at the P tier.**  `BasisStepPB`'s
`natK` branch. -/
theorem declBasisPB_natK {env₁ : Env} (mp : EnvModelM V μ env)
    (h : ConLeche.Semantics.BasisInstallRun env
      ConLeche.BasisKind.natK.declsA env₁) :
    Nonempty (EnvModelM V μ env₁) := by
  rw [show ConLeche.BasisKind.natK.declsA
    = [natA, natZeroA, natSuccA, natRecA] from rfl] at h
  obtain ⟨h1, h2, h3, h4, hnil⟩ := h
  subst hnil
  have hf1 : env.find? natA.name = none :=
    Option.isNone_iff_eq_none.mp h1
  have hwf1 : EnvWF ⟨natA :: env.consts⟩ :=
    EnvWF.cons mp.base2.wf ⟨rfl, rfl, rfl, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
  have hf2 : (⟨natA :: env.consts⟩ : Env).find? natZeroA.name = none :=
    Option.isNone_iff_eq_none.mp h2
  obtain ⟨mp1⟩ := extendNat mp hf1
    (by simp [ConLeche.natLitSupported, ConLeche.natZeroOk,
      show (⟨natA :: env.consts⟩ : Env).find? natZeroName = none
        from hf2]) hwf1
  have hN1 : (⟨natA :: env.consts⟩ : Env).find? natName
      = some natA := by
    rw [ConLeche.Env.find?_cons]; exact if_pos rfl
  have hwf2 : EnvWF ⟨natZeroA :: natA :: env.consts⟩ := by
    refine EnvWF.cons hwf1 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
    show Expr.constsResolve _ natZeroA.toConstantVal.type = true
    have hf : (⟨natZeroA :: natA :: env.consts⟩ : Env).find? natName
        = some natA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hN1
    rw [show natZeroA.toConstantVal.type = Expr.const natName []
      from rfl]
    simp [Expr.constsResolve, hf]
  have hf3 : (⟨natZeroA :: natA :: env.consts⟩ : Env).find?
      natSuccA.name = none := Option.isNone_iff_eq_none.mp h3
  obtain ⟨mp2⟩ := extendNatZero mp1 hN1 hf2
    (by simp [ConLeche.natLitSupported, ConLeche.natSuccOk,
      show (⟨natZeroA :: natA :: env.consts⟩ : Env).find? natSuccName
        = none from hf3]) hwf2
  have hN2 : (⟨natZeroA :: natA :: env.consts⟩ : Env).find? natName
      = some natA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hN1
  have hZ2 : (⟨natZeroA :: natA :: env.consts⟩ : Env).find? natZeroName
      = some natZeroA := by
    rw [ConLeche.Env.find?_cons]; exact if_pos rfl
  have hwf3 : EnvWF ⟨natSuccA :: natZeroA :: natA :: env.consts⟩ := by
    refine EnvWF.cons hwf2 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
    show Expr.constsResolve _ natSuccA.toConstantVal.type = true
    have hf : (⟨natSuccA :: natZeroA :: natA :: env.consts⟩
        : Env).find? natName = some natA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hN2
    rw [show natSuccA.toConstantVal.type
      = Expr.forallE (.const natName [])
        (.const natName []) { pw := .never } from rfl]
    simp [Expr.constsResolve, hf]
  obtain ⟨mp3⟩ := extendNatSucc mp2 hN2 hZ2 hf3  hwf3
  have hN3 : (⟨natSuccA :: natZeroA :: natA :: env.consts⟩
      : Env).find? natName = some natA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hN2
  have hZ3 : (⟨natSuccA :: natZeroA :: natA :: env.consts⟩
      : Env).find? natZeroName = some natZeroA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hZ2
  have hS3 : (⟨natSuccA :: natZeroA :: natA :: env.consts⟩
      : Env).find? natSuccName = some natSuccA := by
    rw [ConLeche.Env.find?_cons]; exact if_pos rfl
  have hf4 : (⟨natSuccA :: natZeroA :: natA :: env.consts⟩
      : Env).find? natRecA.name = none :=
    Option.isNone_iff_eq_none.mp h4
  have hwf4 : EnvWF ⟨natRecA :: natSuccA :: natZeroA :: natA
      :: env.consts⟩ := by
    have hfN : (⟨natRecA :: natSuccA :: natZeroA :: natA
        :: env.consts⟩ : Env).find? natName = some natA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hN3
    have hfZ : (⟨natRecA :: natSuccA :: natZeroA :: natA
        :: env.consts⟩ : Env).find? natZeroName = some natZeroA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hZ3
    have hfS : (⟨natRecA :: natSuccA :: natZeroA :: natA
        :: env.consts⟩ : Env).find? natSuccName = some natSuccA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hS3
    refine EnvWF.cons hwf3 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), ?_,
      (fun _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
    · show Expr.constsResolve _ natRecA.toConstantVal.type = true
      rw [show natRecA.toConstantVal.type
          = Expr.forallE
              (Expr.forallE
                (.const natName []) (.sort (.param uN))
                { pw := .never })
              (Expr.forallE
                (.app (.bvar 0) (.const natZeroName []))
                (Expr.forallE
                  (Expr.forallE
                    (.const natName [])
                    (Expr.forallE
                      (.app (.bvar 2) (.bvar 0))
                      (.app (.bvar 3)
                        (.app (.const natSuccName []) (.bvar 1)))
                      { pw := .ifAllZero [uN] })
                    { pw := .ifAllZero [uN] })
                  (Expr.forallE
                    (.const natName []) (.app (.bvar 3) (.bvar 0))
                    { pw := .ifAllZero [uN] })
                  { pw := .ifAllZero [uN] })
                { pw := .ifAllZero [uN] })
              { pw := .ifAllZero [uN] } from rfl]
      simp only [Expr.constsResolve, hfN, hfZ, hfS, Option.isSome_some,
        Bool.and_self]
    · intro cv mI rP rules heq
      injection heq with h1' h2' h3' h4'
      subst h4'
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr'
      · refine ⟨rfl, ?_, ?_, rfl, fun lvls pins heqf => nomatch heqf⟩
        · subst h1'; rfl
        · show Expr.constsResolve _ natRecZeroRule.rhs = true
          rw [show natRecZeroRule.rhs = _ from rfl]
          simp only [natRecZeroRule, Expr.constsResolve, hfN, hfZ, hfS,
            Option.isSome_some, Bool.and_self]
      · rcases List.mem_cons.mp hr' with rfl | hr''
        · refine ⟨rfl, ?_, ?_, rfl, fun lvls pins heqf => nomatch heqf⟩
          · subst h1'; rfl
          · show Expr.constsResolve _ natRecSuccRule.rhs = true
            have hfR : (⟨natRecA :: natSuccA :: natZeroA :: natA
                :: env.consts⟩ : Env).find? (natName.str "rec")
                = some natRecA := by
              rw [ConLeche.Env.find?_cons]; exact if_pos rfl
            simp only [natRecSuccRule, Expr.constsResolve, hfN, hfZ,
              hfS, hfR, Option.isSome_some, Bool.and_self]
        · exact nomatch hr''
  exact extendNatRec mp3 hN3 hZ3 hS3 hf4  hwf4

end Nat

end ConLeche.Model
