module

public import ConLeche.Model.AxiomPin

public section

/-!
# `DeclAxiomR`'s fourth branch: `ofReduceNat`/`ofReduceBool` at the
validated-annotation currency (task #161, ENDGAME D)

The ENDGAME C seal closed three of `DeclAxiomR`'s four branches and
named the fourth's single blocker — the `ReduceOps` field, which
`Interp/ReduceOps.lean` now supplies.  This file is the branch, and
the seal's prediction held **exactly**:

* **the bits are free.**  The pin's innermost codomain is an `Eq`-spine
  over the *nose-pinned* `Eq` (`ofReduceAxOk`'s own first conjunct), so
  `inferTypeCore_eqSpineS` applies verbatim and `propext_bits`'s three
  moves transpose unchanged — all three binders carry bit `0`, by the
  same telescope collapse.  `Nat`/`Bool` appear only as the spine's
  *type* argument, which the peel never reads: the C seal's correction
  of the B seal's prediction is confirmed;
* **the membership is three `pt_mem_piR_zero_of`s.**  All bits `0`
  makes every product a truth value, the witness is forced to `pt` —
  and `.prf` is the leaf that denotes `pt` in *both* lanes, which is
  why the v1 witness (`Install/Axiom.lean`, `ofReduceKeyS_mem`) ports
  with no re-choice at all: the η-expanded identity `fun a b h => h`
  was refused *there* for the annotated lane's sake, and the P leaf
  inherits that decision;
* **the innermost fibre is where the new field pays.**  The hypothesis
  spine reads to `eqv (op x) y` and the conclusion to `eqv x y`;
  `eq_law` gives both values and `ReduceOps` collapses `op x` to `x`,
  so an inhabitant of the one inhabits the other.  That step — and
  only that step — is what the C seal recorded as unreachable.

With this branch the whole pin bundle closes: `axiomStepPB_of`
(`Interp/FoldP.lean`, where `AxiomStepPB` is stated) assembles the
four branches, and `FoldP`'s `hax` premise is gone.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  BinderMeta inferTypeCore)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {F : Nat}

/-! ## The pinned telescope, inverted -/

/-- **The `ofReduce*` pinned telescope, inverted through both
erasures.**  Every domain, the hypothesis spine and the conclusion
spine are binder-free, so the pin fixes the whole shape and leaves
exactly the three binder names and the three binder metas free —
which is precisely the freedom the bit lemma below removes
(`propext_shapeS`'s pattern at a longer spine). -/
theorem ofReduce_shapeS {n : Name} {type' : Expr}
    (hn : n = ConLeche.ofReduceNatName ∨ n = ConLeche.ofReduceBoolName)
    (h : type'.erasePw
      = (ConLeche.ofReducePinA n).type.erasePw) :
    ∃ m₁ m₂ m₃,
      type' = .forallE
        (.const (ConLeche.reduceElemName (ConLeche.ofReduceOp n)) [])
        (.forallE
          (.const (ConLeche.reduceElemName (ConLeche.ofReduceOp n)) [])
          (.forallE
            (.app (.app (.app (.const eqName [.succ .zero])
                (.const (ConLeche.reduceElemName
                  (ConLeche.ofReduceOp n)) []))
              (.app (.const (ConLeche.ofReduceOp n) []) (.bvar 1)))
              (.bvar 0))
            (.app (.app (.app (.const eqName [.succ .zero])
                (.const (ConLeche.reduceElemName
                  (ConLeche.ofReduceOp n)) []))
              (.bvar 2)) (.bvar 1)) m₃) m₂) m₁ := by
  rw [ConLeche.Verify.ofReducePin_type hn] at h
  simp only [Expr.mkAppN, Expr.erasePw] at h
  obtain ⟨ty₁, b₁, m₁, rfl, hty₁, hb₁⟩ := erasePwNames_forallE_invS h
  obtain rfl := erasePwNames_const_invS hty₁
  obtain ⟨ty₂, b₂, m₂, rfl, hty₂, hb₂⟩ := erasePwNames_forallE_invS hb₁
  obtain rfl := erasePwNames_const_invS hty₂
  obtain ⟨ty₃, b₃, m₃, rfl, hty₃, hb₃⟩ := erasePwNames_forallE_invS hb₂
  -- the hypothesis spine
  obtain ⟨f, a, rfl, hf, ha⟩ := erasePwNames_app_invS hty₃
  obtain ⟨f', a', rfl, hf', ha'⟩ := erasePwNames_app_invS hf
  obtain ⟨f'', a'', rfl, hf'', ha''⟩ := erasePwNames_app_invS hf'
  obtain rfl := erasePwNames_const_invS hf''
  obtain rfl := erasePwNames_const_invS ha''
  obtain ⟨g, gb, rfl, hg, hgb⟩ := erasePwNames_app_invS ha'
  obtain rfl := erasePwNames_const_invS hg
  obtain rfl := erasePwNames_bvar_invS hgb
  obtain rfl := erasePwNames_bvar_invS ha
  -- the conclusion spine
  obtain ⟨p, q, rfl, hp, hq⟩ := erasePwNames_app_invS hb₃
  obtain ⟨p', q', rfl, hp', hq'⟩ := erasePwNames_app_invS hp
  obtain ⟨p'', q'', rfl, hp'', hq''⟩ := erasePwNames_app_invS hp'
  obtain rfl := erasePwNames_const_invS hp''
  obtain rfl := erasePwNames_const_invS hq''
  obtain rfl := erasePwNames_bvar_invS hq'
  obtain rfl := erasePwNames_bvar_invS hq
  exact ⟨m₁, m₂, m₃, rfl⟩

/-! ## The bits -/

/-- **THE NAMED FACT, at `ofReduce*`.**  Every binder of the stored
type carries bit `0`, at every assignment.  `propext_bits` verbatim:
the innermost codomain is an `Eq`-spine over the nose-pinned `Eq`
(`inferTypeCore_eqSpineS`), and the telescope collapse
(`imax x y = 0 ↔ y = 0`) carries that bit outward through the two
remaining binders — one fact, not three.  Note what is *not* used: the
element type is the spine's type argument, and the peel never reads
it, so nothing about the stored `Nat`/`Bool` enters. -/
theorem ofReduce_bits (hμ : μ.verifiedChecks = true)
    (hEq : env.find? eqName = some eqA)
    {E c : Name} {m₁ m₂ m₃ : BinderMeta}
    {d : Nat} {stype : Expr}
    (hrun : inferTypeCore μ env F d
      (.forallE (.const E [])
        (.forallE (.const E [])
          (.forallE
            (.app (.app (.app (.const eqName [.succ .zero])
                (.const E [])) (.app (.const c []) (.bvar 1)))
              (.bvar 0))
            (.app (.app (.app (.const eqName [.succ .zero])
                (.const E [])) (.bvar 2)) (.bvar 1)) m₃) m₂) m₁)
      = .ok stype) (φ : Name → Nat) :
    pwBit φ m₁.pw = 0 ∧ pwBit φ m₂.pw = 0 ∧ pwBit φ m₃.pw = 0 := by
  match F, hrun with
  | 0, hrun => rw [ConLeche.inferTypeCore_zero] at hrun; exact nomatch hrun
  | F1 + 1, hrun =>
  obtain ⟨tty1, u1, bt1, v1, -, -, hbt1, hens1, hpw1, rfl⟩ :=
    ConLeche.inferTypeCore_forall_inv hrun
  match F1, hbt1 with
  | 0, hbt1 => rw [ConLeche.inferTypeCore_zero] at hbt1; exact nomatch hbt1
  | F2 + 1, hbt1 =>
  obtain ⟨tty2, u2, bt2, v2, -, -, hbt2, hens2, hpw2, rfl⟩ :=
    ConLeche.inferTypeCore_forall_inv hbt1
  match F2, hbt2 with
  | 0, hbt2 => rw [ConLeche.inferTypeCore_zero] at hbt2; exact nomatch hbt2
  | F3 + 1, hbt2 =>
  obtain ⟨tty3, u3, bt3, v3, -, -, hbt3, hens3, hpw3, rfl⟩ :=
    ConLeche.inferTypeCore_forall_inv hbt2
  obtain rfl : bt3 = .sort .zero := inferTypeCore_eqSpineS hEq hbt3
  obtain rfl : v3 = .zero := ensureSortCore_sort_eq hens3
  have hb3 : pwBit φ m₃.pw = 0 := by
    rw [← hpw3 hμ]; exact (pwBit_zeronessOf φ _).mpr rfl
  obtain rfl : v2 = .imax u3 .zero := ensureSortCore_sort_eq hens2
  have hb2 : pwBit φ m₂.pw = 0 := by
    rw [← hpw2 hμ]; exact (pwBit_zeronessOf φ _).mpr (by simp [Level.eval])
  obtain rfl : v1 = .imax u2 (.imax u3 .zero) :=
    ensureSortCore_sort_eq hens1
  have hb1 : pwBit φ m₁.pw = 0 := by
    rw [← hpw1 hμ]; exact (pwBit_zeronessOf φ _).mpr (by simp [Level.eval])
  exact ⟨hb1, hb2, hb3⟩

/-! ## The gates, unpacked -/

/-- `ofReduceAxOk`'s four conjuncts, in the forms the membership reads
(the v1 key's own unpacking, one file over). -/
theorem ofReduce_gatesS {cvA : ConstantVal}
    (hok : ConLeche.ofReduceAxOk env cvA = true) :
    env.find? eqName = some eqA ∧
    ConLeche.reduceElemOk env (ConLeche.ofReduceOp cvA.name) = true ∧
    (∃ cvR, env.find? (ConLeche.ofReduceOp cvA.name)
        = some (.axiomInfo cvR) ∧
      ConstantVal.matchesPin cvR
        (ConLeche.reduceOpCvA (ConLeche.ofReduceOp cvA.name)) = true) ∧
    cvA.type.erasePw
      = (ConLeche.ofReducePinA cvA.name).type.erasePw := by
  simp only [ConLeche.ofReduceAxOk, Bool.and_eq_true,
    decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hEq, helem⟩, hstored⟩, hpin⟩ := hok
  refine ⟨hEq, helem, ?_, ?_⟩
  · rw [ConLeche.reduceStoredOk] at hstored
    cases hf : env.find? (ConLeche.ofReduceOp cvA.name) with
    | none => rw [hf] at hstored; exact nomatch hstored
    | some ci =>
      rw [hf] at hstored
      cases ci with
      | axiomInfo cvR => exact ⟨cvR, rfl, hstored⟩
      | _ => exact nomatch hstored
  · simp only [ConstantVal.matchesPin, Bool.and_eq_true,
      beq_iff_eq] at hpin
    exact hpin.2

/-! ## The membership -/

/-- **`ofReduce*`'s canonical proof inhabits its stored type's
reading.**  Three `pt_mem_piR_zero_of`s (every bit is `0`, so every
product is a truth value); the innermost fibre is where `ReduceOps`
pays: the hypothesis spine's value is `eqv (op x) y`, the conclusion's
is `eqv x y`, and the field says those are the same set. -/
theorem ofReduce_mem (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {cvA : ConstantVal} (hok : ConLeche.ofReduceAxOk env cvA = true)
    (hor : cvA.name = ConLeche.ofReduceNatName ∨
      cvA.name = ConLeche.ofReduceBoolName)
    {d : Nat} {stype : Expr}
    (hrun : inferTypeCore μ env F d cvA.type = .ok stype)
    (ψ : Name → Nat) (ta : AnnotTerm)
    (hta : denoteMeta mp.base2.acval env ψ 0 cvA.type = some ta)
    (ρ : Nat → V) :
    interp V ρ (AnnotTerm.prf) ∈ˢ interp V ρ ta := by
  obtain ⟨hEq, helem, ⟨cvR, hfR, hmpR⟩, hApinT⟩ := ofReduce_gatesS hok
  obtain ⟨ciE, hfE, hlpE, htyE⟩ := ConLeche.Verify.reduceElem_sort helem
  obtain ⟨-, hlpR⟩ := ConLeche.Verify.matchesPin_invT hmpR
  rw [show (ConLeche.reduceOpCvA
      (ConLeche.ofReduceOp cvA.name)).levelParams = [] from by
    unfold ConLeche.reduceOpCvA; split <;> rfl] at hlpR
  have hmemOp : ConLeche.ofReduceOp cvA.name ∈ ConLeche.reduceOpNames := by
    unfold ConLeche.ofReduceOp; split <;> decide
  obtain ⟨m₁, m₂, m₃, hsh⟩ := ofReduce_shapeS hor hApinT
  rw [hsh] at hrun hta
  obtain ⟨hb₁, hb₂, hb₃⟩ := ofReduce_bits hμ hEq hrun ψ
  -- the `Eq` former's one level parameter is pinned to `1`
  have heqψ : Level.substFn ψ eqA.toConstantVal.levelParams
      [Level.zero.succ] uN = 1 := rfl
  have hEd : ∀ e, denoteMeta mp.base2.acval env ψ e
      (.const (ConLeche.reduceElemName (ConLeche.ofReduceOp cvA.name)) [])
      = some (mp.base2.acval
          (ConLeche.reduceElemName (ConLeche.ofReduceOp cvA.name)) ψ) :=
    fun e => denoteMeta_levelless_const hfE hlpE
  have hOd : ∀ e, denoteMeta mp.base2.acval env ψ e
      (.const (ConLeche.ofReduceOp cvA.name) [])
      = some (mp.base2.acval (ConLeche.ofReduceOp cvA.name) ψ) :=
    fun e => denoteMeta_levelless_const hfR
      (show (ConstantInfo.axiomInfo cvR).toConstantVal.levelParams = []
        from hlpR)
  have hQd : ∀ e, denoteMeta mp.base2.acval env ψ e
      (.const eqName [Level.zero.succ])
      = some (mp.base2.acval eqName (Level.substFn ψ
          eqA.toConstantVal.levelParams [Level.zero.succ])) :=
    fun e => denoteMeta_const hEq rfl
  -- the stored type's reading, at the bits the run fixes
  have hden : denoteMeta mp.base2.acval env ψ 0
      (.forallE
        (.const (ConLeche.reduceElemName (ConLeche.ofReduceOp cvA.name)) [])
        (.forallE
          (.const (ConLeche.reduceElemName
            (ConLeche.ofReduceOp cvA.name)) [])
          (.forallE
            (.app (.app (.app (.const eqName [.succ .zero])
                (.const (ConLeche.reduceElemName
                  (ConLeche.ofReduceOp cvA.name)) []))
              (.app (.const (ConLeche.ofReduceOp cvA.name) []) (.bvar 1)))
              (.bvar 0))
            (.app (.app (.app (.const eqName [.succ .zero])
                (.const (ConLeche.reduceElemName
                  (ConLeche.ofReduceOp cvA.name)) []))
              (.bvar 2)) (.bvar 1)) m₃) m₂) m₁)
      = some (.pi 0 0
          (mp.base2.acval (ConLeche.reduceElemName
            (ConLeche.ofReduceOp cvA.name)) ψ)
          (.pi 0 0
            (mp.base2.acval (ConLeche.reduceElemName
              (ConLeche.ofReduceOp cvA.name)) ψ)
            (.pi 0 0
              (.app (.app (.app (mp.base2.acval eqName
                    (Level.substFn ψ eqA.toConstantVal.levelParams
                      [Level.zero.succ]))
                  (mp.base2.acval (ConLeche.reduceElemName
                    (ConLeche.ofReduceOp cvA.name)) ψ))
                (.app (mp.base2.acval (ConLeche.ofReduceOp cvA.name) ψ)
                  (.bvar 1))) (.bvar 0))
              (.app (.app (.app (mp.base2.acval eqName
                    (Level.substFn ψ eqA.toConstantVal.levelParams
                      [Level.zero.succ]))
                  (mp.base2.acval (ConLeche.reduceElemName
                    (ConLeche.ofReduceOp cvA.name)) ψ))
                (.bvar 2)) (.bvar 1))))) := by
    simp [denoteMeta_forallE, denoteMeta_app, denoteMeta_fvar,
      Expr.instantiate1, hEd, hOd, hQd, hb₁, hb₂, hb₃]
  obtain rfl : ta = _ := Option.some.inj (hta.symm.trans hden)
  -- the three leaves' interpretations do not read the environment
  have hclE : ∀ ρ' : Nat → V,
      interp V ρ' (mp.base2.acval
          (ConLeche.reduceElemName (ConLeche.ofReduceOp cvA.name)) ψ)
        = interp V ρ (mp.base2.acval
          (ConLeche.reduceElemName (ConLeche.ofReduceOp cvA.name)) ψ) :=
    fun ρ' => acval_interp_closedC mp.base2 _ ψ ρ' ρ
  have hclO : ∀ ρ' : Nat → V,
      interp V ρ' (mp.base2.acval (ConLeche.ofReduceOp cvA.name) ψ)
        = interp V ρ (mp.base2.acval (ConLeche.ofReduceOp cvA.name) ψ) :=
    fun ρ' => acval_interp_closedC mp.base2 _ ψ ρ' ρ
  have hclQ : ∀ ρ' : Nat → V,
      interp V ρ' (mp.base2.acval eqName
          (Level.substFn ψ eqA.toConstantVal.levelParams
            [Level.zero.succ]))
        = interp V ρ (mp.base2.acval eqName
          (Level.substFn ψ eqA.toConstantVal.levelParams
            [Level.zero.succ])) :=
    fun ρ' => acval_interp_closedC mp.base2 _ _ ρ' ρ
  -- the element type inhabits `Sort 1`
  have hEmem : interp V ρ (mp.base2.acval
      (ConLeche.reduceElemName (ConLeche.ofReduceOp cvA.name)) ψ)
      ∈ˢ (univ 1 : V) := by
    have h := mp.mem_type ciE (ConLeche.Semantics.Env.find?_mem hfE) ψ
      (.sort 1) (by rw [htyE, denoteMeta_sort]; rfl) ρ
    rwa [ConLeche.Semantics.Env.find?_name hfE, interp_sort] at h
  -- three `Prop`-level products, all `pt`-inhabited
  show (pt : V) ∈ˢ _
  simp only [interp_pi, interp_app, interp_bvar, cons_zero,
    cons_succ, hclE, hclO, hclQ]
  refine pt_mem_piR_zero_of fun x hx => ?_
  refine pt_mem_piR_zero_of fun y hy => ?_
  refine pt_mem_piR_zero_of fun h hh => ?_
  -- **the field pays here**: the trusted operation is the identity
  have hopx : SetTheory.app (interp V ρ
      (mp.base2.acval (ConLeche.ofReduceOp cvA.name) ψ)) x = x :=
    (mp.reduce_ops _ hmemOp cvR hfR hmpR).2 ψ ρ x hx
  rw [hopx] at hh
  rw [(mp.eq_law hEq _).1 ρ _ x y (by rw [heqψ]; exact hEmem) hx hy]
    at hh
  rw [(mp.eq_law hEq _).1 ρ _ x y (by rw [heqψ]; exact hEmem) hx hy]
  rw [mem_eqv hh]
  exact pt_mem_eqv_self y

/-! ## The branch -/

/-- **The `ofReduce*` branch, discharged.**  The leaf is `.prf`, the
canonical proof — the same witness the v1 key installs
(`ofReduceKeyS_mem`), which is why every syntactic obligation is `rfl`
or a `simp` on a leaf clause and the whole content is the
membership. -/
theorem axiomOfReduce (hμ : μ.verifiedChecks = true)
    (mp : EnvModelM V μ env) {cv : ConstantVal} {type' : Expr}
    (hcv : ConstantValRun μ F env cv type')
    (hor : cv.name = ConLeche.ofReduceNatName ∨
      cv.name = ConLeche.ofReduceBoolName)
    (hok : ConLeche.ofReduceAxOk env ⟨cv.name, cv.levelParams, type'⟩
      = true) :
    Nonempty (EnvModelM V μ
      ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts⟩) := by
  have hcv' := hcv
  obtain ⟨hfind, hnres, hpshape, hnd, hlbt, hitf, hann, htp, htr,
    hrunT⟩ := hcv'
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann hitf hlbt
  have hfresh : env.find? cv.name = none :=
    Option.isNone_iff_eq_none.mp hfind
  obtain ⟨stype, usort, hst, hens⟩ := hrunT
  have hwfc : ConLeche.EnvWF ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
      env.consts⟩ := by
    refine ConLeche.EnvWF.cons mp.base2.wf
      ⟨htf', htp, Expr.constsResolve_mono htr, hbt', ?_, ?_, ?_, ?_⟩
    · intro cv2 value2 hint2 heq; exact nomatch heq
    · intro cv2 mI rP rules heq; exact nomatch heq
    · intro tbl heq; exact nomatch heq
    · intro cv2 caps heq; exact nomatch heq
  refine harvestAxiom (V := V) hμ mp hcv
    (A := fun _ => AnnotTerm.prf) (fun _ => trivial)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => by simp)
    (fun _ _ => by simp) ?_
    (by rcases hor with h | h <;> rw [h] <;> decide)
  intro ψ ta hta ρ
  exact ofReduce_mem hμ mp hok hor hst ψ ta hta ρ

-- (`axiomStepPB_of`, which assembles these four branches, lands in
-- `Interp/FoldP.lean`: `AxiomStepPB` is stated there, beside the two
-- bundles still routed.)

end ConLeche.Model
