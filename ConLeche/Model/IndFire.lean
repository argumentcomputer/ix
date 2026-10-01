module

public import ConLeche.Model.IndAnnotMem
/- `ConLeche.Kernel.PropWhen` seals its representation on purpose (the
`Std.HashMap` pattern, task #194): the datum's module is `public` but not
`@[expose]`d, so a `cases`-then-`rfl` proof cannot see the reduct.
`import all` restores that view HERE only. -/
import all ConLeche.Kernel.PropWhen
import ConLeche.Model.Annot.BitLevels

public section

/-!
# The firing stage, at the reading (task #161, IND TIER part 7)

`fireS`'s transpose (`Install/IndStagesS.lean:1108`): the checked
`iota_j` equation, fired at the zipped chain — the theorem's inhabitant
applied along the fit lands in the interpreted `Eq`-spine, the spine
computes to the truth set through `eq_law`, and `mem_eqv` reads the
equation off.

Three deltas against v1, all of them the P tier's own currency:

* **the slot's universe membership is read top-down, not along the
  chain.**  v1 calls `annotOkV_descend` — the descent along the *value
  chain* — to grade the statement's body at `chainE V ρ zs`.  Part 4
  recorded why that shape cannot be transposed (`IndGradeP.lean`: the
  chain step charges for the arguments' gradings, which
  `RecRuleLaw`'s interp-equality half does not have).  The route that
  works is the one `wellDenotedV_tower_slot` already takes —
  `wellDenotedV_tower_body` below descends **top-down along the satisfying
  environment**, spending `Sat` and asking the arguments for nothing;
* **the `Eq` former's product is at a positive kind**, and that is a
  computation, not a hypothesis: the pinned type's outer binder carries
  `PropWhen.never`, so its bit is `pwBit φ .never = 1`
  (`denoteMeta_forallE` reads the bit off the binder meta).  The squash
  branch of the app package is then refuted exactly as the part-6 probe
  refutes it (`eq_pt_of_mem_piR_zero` + `not_pt_mem_piR_pos`), so
  `piR_dom_unique` applies with no side condition;
* **the sides pack is a pair of recorded runs, not a derivation
  bundle.**  `sidesMem` is four lines: `IotaRuns` carries
  `inferTypeCore lhsS` and `isDefEqCore … αS` outright, and
  `InferClaim`/`DefEqClaim` convert them at the frame's own
  context.  v1's `sidesMemS` had to rebuild three `CtxOkR`s and fire
  the quantified-context packs; here `ctxOk_of_walked_openers` has
  already produced the context the stages share.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  isDefEqCore inferTypeCore)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## The tower's body, graded top-down -/

/-- **A tower's body is graded at any satisfying environment**
(`wellDenotedV_tower_slot`'s companion, same induction, same reason): the
`.pi` split's extension environment is `cons (ρ' q) (fun j => ρ' (j + q + 1))
= fun j => ρ' (j + q)` on the nose, so the descent spends the
satisfaction and charges the arguments nothing.

This is what replaces v1's `annotOkV_descend` at the firing stage: that
lemma descends along the *value chain* and would need the fired spine
graded — the premise `RecRuleLaw`'s interp-equality half deliberately
does not carry. -/
theorem wellDenotedV_tower_body :
    ∀ (k : Nat) {T : AnnotTerm} {Γ : List AnnotTerm} {R : AnnotTerm},
      PiTeleAV k T Γ R → ∀ {ρ' : Nat → V},
      WellDenotedV V (fun j => ρ' (j + k)) T →
      (∀ q, q < k →
        ρ' q ∈ˢ interp V (fun j => ρ' (j + q + 1)) (Γ.getD q default)) →
      WellDenotedV V ρ' R := by
  intro k
  induction k with
  | zero =>
    intro T Γ R h ρ' hokT _
    cases h
    exact hokT
  | succ k ih =>
    intro T Γ R h ρ' hokT hmem
    obtain ⟨u, v, A, B, Γ', rfl, rfl, htail⟩ := h.succ_inv
    have hΓ'len : Γ'.length = k := htail.length
    have hgetA : (Γ' ++ [A]).getD k default = A := by
      rw [List.getD, List.getElem?_append_right (by omega), hΓ'len]
      simp
    have hokT' : WellDenotedV V (fun j => ρ' (j + k + 1))
        (AnnotTerm.pi u v A B) := hokT
    have hmemk : ρ' k ∈ˢ interp V (fun j => ρ' (j + k + 1)) A := by
      have := hmem k (by omega)
      rwa [hgetA] at this
    have henv : cons (ρ' k) (fun j => ρ' (j + k + 1))
        = (fun j => ρ' (j + k)) := by
      funext j
      cases j with
      | zero =>
        show cons (ρ' k) (fun j => ρ' (j + k + 1)) 0 = ρ' (0 + k)
        rw [cons_zero]
        congr 1
        omega
      | succ j =>
        show cons (ρ' k) (fun j => ρ' (j + k + 1)) (j + 1)
          = ρ' (j + 1 + k)
        rw [cons_succ]
        show ρ' (j + k + 1) = ρ' (j + 1 + k)
        congr 1
        omega
    have hokB : WellDenotedV V (fun j => ρ' (j + k)) B := by
      refine ⟨?_, ?_⟩
      · have h := ((WellDenoted_pi V (fun j => ρ' (j + k + 1)) u v A B)
          ▸ hokT'.1).2 (ρ' k) hmemk
        rwa [henv] at h
      · have h := ((AnnotValid_pi V (fun j => ρ' (j + k + 1)) u v A B)
          ▸ hokT'.2).2.1 (ρ' k) hmemk
        rwa [henv] at h
    have hgetΓ' : ∀ q, q < k →
        (Γ' ++ [A]).getD q default = Γ'.getD q default := by
      intro q hq
      rw [List.getD, List.getD, List.getElem?_append_left (by omega)]
    exact ih htail hokB (fun q hq => by
      have := hmem q (by omega)
      rwa [hgetΓ' q hq] at this)

/-- **The tower's body, graded at a `Sat`-satisfied context.** -/
theorem wellDenotedV_tower_body_sat {k : Nat} {T : AnnotTerm} {Γ : List AnnotTerm}
    {R : AnnotTerm} (htower : PiTeleAV k T Γ R) {ρ' : Nat → V}
    (hokT : WellDenotedV V (fun j => ρ' (j + k)) T) (hsat : Sat V Γ ρ') :
    WellDenotedV V ρ' R := by
  have hΓlen : Γ.length = k := htower.length
  refine wellDenotedV_tower_body k htower hokT (fun q hq => ?_)
  refine hsat q (Γ.getD q default) ?_
  rw [List.getD]
  rcases hg : Γ[q]? with _ | A
  · rw [List.getElem?_eq_none_iff] at hg; omega
  · rfl

/-! ## Applying along a fit, value-headed -/

/-- **An inhabited telescope's residual is inhabited along a fit** —
`TeleFitV.appN_val` at the reading, weakened from "the application
lands in the residual" to "the residual is nonempty", which is
**strictly what the firing stage spends**: `mem_eqv` reads the equation
off *any* member of the truth value.

The weakening is not a convenience, it is what makes the transpose
possible.  v1 applies the theorem's inhabitant along the fit through
`app_mem_piC`, which has no regime; `app_mem_piR`'s squash branch needs
the codomain fibres to be truth values, and that fact rides
`AnnotValid`'s `.pi` clause — which the fit's *substituted* tower
`B.inst a` cannot carry, because `AnnotValid_inst` charges for the
substituted argument's own validity and `RecRuleLaw`'s
interp-equality half deliberately carries no grading of the fired
spine (the part-4 finding, `IndGradeP.lean`).  Nonemptiness needs
neither: at `v = 0` the product **is** the truth value of "every
fibre is inhabited" (`piR_zero`), so membership hands the fibre's
inhabitant over directly. -/
theorem teleFitPA_nonempty {ρ : Nat → V} :
    ∀ {T rest : AnnotTerm} {as : List AnnotTerm},
      TeleFitPA V ρ T as rest →
      (∃ x : V, x ∈ˢ interp V ρ T) →
      ∃ y : V, y ∈ˢ interp V ρ rest := by
  intro T rest as h
  induction h with
  | nil => exact id
  | @cons u v A B rest a as hmem htail ih =>
    intro hx
    obtain ⟨x, hx⟩ := hx
    rw [interp_pi] at hx
    refine ih ?_
    rw [interp_inst0]
    by_cases hv : v = 0
    · subst hv
      rw [piR_zero] at hx
      exact of_mem_truthVal hx _ hmem
    · exact ⟨_, app_mem_piR_pos hv hx hmem⟩

/-! ## The `Eq` former's firing key -/

/-- **What the firing stage needs of the environment** (`EqFormerKeyV`
at the reading): the pinned `Eq` former's leaf is closed, and inhabits
its own type's reading, graded. -/
def EqFormerKey {env : Env} (m : EnvModel V env) (φ : Name → Nat) :
    Prop :=
  ∀ us : List Level,
    us.length = eqA.toConstantVal.levelParams.length →
    ∀ T : AnnotTerm,
      denoteMeta m.acval env φ 0
        (eqA.toConstantVal.type.instantiateLevelParams
          eqA.toConstantVal.levelParams us) = some T →
      ∀ ρ : Nat → V,
        interp V ρ (m.acval eqName
            (Level.substFn φ eqA.toConstantVal.levelParams us))
          ∈ˢ interp V ρ T ∧ WellDenotedV V ρ T

/-- A stored `Eq` gives the firing key — the two `EnvModelM` type fields
at the pinned constant. -/
theorem eqFormerKey {env : Env} (mp : EnvModelM V μ env)
    (heqfE : env.find? eqName = some eqA) :
    EqFormerKey mp.base2 φ := by
  intro us _hlen T hT ρ
  have hmem := ConLeche.Semantics.Env.find?_mem heqfE
  have hname := ConLeche.Semantics.Env.find?_name heqfE
  have hT' : denoteMeta mp.base2.acval env
      (Level.substFn φ eqA.toConstantVal.levelParams us) 0
      eqA.toConstantVal.type = some T := by
    rw [← denotePInstLevels]
    exact hT
  refine ⟨?_, mp.type_wellDenotedV eqA hmem _ T hT' ρ⟩
  have h := mp.mem_type eqA hmem
    (Level.substFn φ eqA.toConstantVal.levelParams us) T hT' ρ
  rwa [hname] at h

/-! ## The firing stage -/

set_option maxHeartbeats 3200000 in
/-- **The firing stage, at the reading** (`fireS`): the checked
equation, fired at the zipped chain.  The statement's residual is
inhabited along the fit (`teleFitPA_nonempty`), it computes to the
interpreted equation spine through `eq_law`, and `mem_eqv` reads the
equation off.

The equation slot's universe membership — v1's one place for
`annotOkV_descend` — is produced here by `wellDenotedV_tower_body_sat`
(top-down along the satisfying environment) plus graph rigidity of the
pinned `Eq` former, whose product is positive-kind because the stored
type's outer binder carries `PropWhen.never`. -/
theorem fire {m : EnvModel V env} {ψ' : Name → Nat}
    (hkey : EqFormerKey m ψ') (heqlaw : EqLaw m)
    (heqfE : env.find? eqName = some eqA)
    {K : Nat}
    {Tstmt : AnnotTerm} {Γs : List AnnotTerm} {Rbody : AnnotTerm}
    (htowerS : PiTeleAV K Tstmt Γs Rbody)
    (hstmtAnnot : ∀ σ : Nat → V, WellDenotedV V σ Tstmt)
    (hstmtInhab : ∀ σ : Nat → V, ∃ pv : V, pv ∈ˢ interp V σ Tstmt)
    {tbody : Expr} {ℓA : Level} {αS lhsS rhsS : Expr}
    (hRbody : denoteMeta m.acval env ψ' K tbody = some Rbody)
    (htbody : tbody
      = Expr.mkAppN (.const eqName [ℓA]) [αS, lhsS, rhsS])
    {zs : List AnnotTerm} {ρ : Nat → V}
    (hsides : ∀ vα vL vR : AnnotTerm,
      denoteMeta m.acval env ψ' K αS = some vα →
      denoteMeta m.acval env ψ' K lhsS = some vL →
      denoteMeta m.acval env ψ' K rhsS = some vR →
      interp V (chain V ρ zs) vL ∈ˢ interp V (chain V ρ zs) vα ∧
        interp V (chain V ρ zs) vR ∈ˢ interp V (chain V ρ zs) vα)
    (hzslen : zs.length = K)
    (hsat : Sat V Γs (chain V ρ zs))
    (hfit : TeleFitPA V ρ Tstmt zs
      (ConLeche.Model.AnnotTerm.instSeq zs (K - 1) Rbody)) :
    ∃ vα vL vR : AnnotTerm,
      denoteMeta m.acval env ψ' K αS = some vα ∧
      denoteMeta m.acval env ψ' K lhsS = some vL ∧
      denoteMeta m.acval env ψ' K rhsS = some vR ∧
      interp V (chain V ρ zs) vL
        = interp V (chain V ρ zs) vR := by
  -- read the equation spine apart
  rw [htbody] at hRbody
  obtain ⟨vEq, vs3, hvEq, hsp3, rfl⟩ := denoteMeta_mkAppN_inv hRbody
  obtain ⟨vα, vL, vR, rfl, hvα, hvL, hvR⟩ : ∃ vα vL vR,
      vs3 = [vα, vL, vR] ∧
      denoteMeta m.acval env ψ' K αS = some vα ∧
      denoteMeta m.acval env ψ' K lhsS = some vL ∧
      denoteMeta m.acval env ψ' K rhsS = some vR := by
    cases hsp3 with
    | cons hα htail =>
      cases htail with
      | cons hL htail2 =>
        cases htail2 with
        | cons hR htail3 =>
          cases htail3 with
          | nil => exact ⟨_, _, _, rfl, hα, hL, hR⟩
  -- the head is the stored `Eq`'s annotated valuation
  have hvEq' : vEq = m.acval eqName
      (Level.substFn ψ' eqA.toConstantVal.levelParams [ℓA]) := by
    rw [denoteMeta_const heqfE
      (show ([ℓA] : List Level).length
        = eqA.toConstantVal.levelParams.length from rfl)] at hvEq
    exact (Option.some.inj hvEq).symm
  -- the statement body, graded at the fired chain (top-down)
  have hokBody : WellDenotedV V (chain V ρ zs)
      (AnnotTerm.mkAppN vEq [vα, vL, vR]) :=
    wellDenotedV_tower_body_sat htowerS (hstmtAnnot _) hsat
  -- the pinned `Eq` type's reading at the stored level
  have hbit : pwBit ψ' ConLeche.PropWhen.never = 1 := rfl
  have hTden : denoteMeta m.acval env ψ' 0
      (eqA.toConstantVal.type.instantiateLevelParams
        eqA.toConstantVal.levelParams [ℓA])
      = some (.pi 0 1 (.sort (ℓA.eval ψ'))
          (.pi 0 1 (.bvar 0) (.pi 0 1 (.bvar 1) (.sort 0)))) := by
    have hinst : eqA.toConstantVal.type.instantiateLevelParams
        eqA.toConstantVal.levelParams [ℓA]
        = .forallE (.sort ℓA)
            (.forallE (.bvar 0)
              (.forallE (.bvar 1)
                (.sort .zero) ⟨.never⟩)
              ⟨.never⟩) ⟨.never⟩ := rfl
    have hb1 : (Expr.forallE (.bvar 0)
        (.forallE (.bvar 1)
          (.sort .zero) ⟨.never⟩) ⟨.never⟩).instantiate1
        (.fvar 0 (.sort ℓA))
        = .forallE
            (.fvar 0 (.sort ℓA))
            (.forallE
              (.fvar 0 (.sort ℓA))
              (.sort .zero) ⟨.never⟩)
            ⟨.never⟩ := rfl
    have hb2 : (Expr.forallE
        (.fvar 0 (.sort ℓA))
        (.sort .zero) ⟨.never⟩).instantiate1
        (.fvar 1
          (.fvar 0 (.sort ℓA)))
        = .forallE
            (.fvar 0 (.sort ℓA))
            (.sort .zero) ⟨.never⟩ := rfl
    have hb3 : (Expr.sort .zero).instantiate1
        (.fvar 2
          (.fvar 0 (.sort ℓA)))
        = .sort .zero := rfl
    rw [hinst, denoteMeta_forallE, denoteMeta_sort, hb1, denoteMeta_forallE,
      denoteMeta_fvar, hb2, denoteMeta_forallE, denoteMeta_fvar, hb3,
      denoteMeta_sort]
    simp only [hbit]
    rfl
  have hmemEq := hkey [ℓA] rfl _ hTden (chain V ρ zs)
  have hEqIn2 : interp V (chain V ρ zs) vEq
      ∈ˢ piR 1 (univ (ℓA.eval ψ'))
        (fun x => interp V (cons x (chain V ρ zs))
          (AnnotTerm.pi 0 1 (.bvar 0) (.pi 0 1 (.bvar 1) (.sort 0)))) := by
    have h3 := hmemEq.1
    rw [interp_pi, interp_sort] at h3
    rw [hvEq']
    exact h3
  -- the slot's universe membership, by graph rigidity
  have hαuniv : interp V (chain V ρ zs) vα
      ∈ˢ (univ (ℓA.eval ψ') : V) := by
    have hokB2 := hokBody.1
    rw [show AnnotTerm.mkAppN vEq [vα, vL, vR]
        = .app (.app (.app vEq vα) vL) vR from rfl,
      WellDenoted_app] at hokB2
    have h1 := hokB2.1
    rw [WellDenoted_app] at h1
    have h2 := h1.1
    rw [WellDenoted_app] at h2
    obtain ⟨-, -, v', A', B', hEqIn, hαIn, -⟩ := h2
    have hv' : v' ≠ 0 := by
      intro hz
      subst hz
      exact not_pt_mem_piR_pos (V := V) Nat.one_ne_zero
        (by rw [← eq_pt_of_mem_piR_zero hEqIn]; exact hEqIn2)
    have hAA : univ (ℓA.eval ψ') = A' :=
      piR_dom_unique Nat.one_ne_zero hv' hEqIn2 hEqIn
    rw [hAA]
    exact hαIn
  -- the sides' memberships, at the slot the rigidity just named
  obtain ⟨hLmem, hRmem⟩ := hsides vα vL vR hvα hvL hvR
  -- the residual computes to the interpreted equation
  have hEqcl : ∀ k : Nat, AnnotTerm.liftN 1 vEq k = vEq := by
    rw [hvEq']
    exact m.acval_closed _ _
  have hlaw := (heqlaw heqfE
    (Level.substFn ψ' eqA.toConstantVal.levelParams [ℓA])).1
  have hresid : interp V ρ
      (ConLeche.Model.AnnotTerm.instSeq zs (K - 1)
        (AnnotTerm.mkAppN vEq [vα, vL, vR]))
      = eqv (interp V (chain V ρ zs) vL)
        (interp V (chain V ρ zs) vR) := by
    rw [show K - 1 = zs.length - 1 from by rw [hzslen],
      instSeqAV_mkAppN, instSeqAV_eq_self_of_closed hEqcl]
    show interp V ρ (AnnotTerm.mkAppN vEq
        [ConLeche.Model.AnnotTerm.instSeq zs (zs.length - 1) vα,
         ConLeche.Model.AnnotTerm.instSeq zs (zs.length - 1) vL,
         ConLeche.Model.AnnotTerm.instSeq zs (zs.length - 1) vR]) = _
    show SetTheory.app (SetTheory.app (SetTheory.app
        (interp V ρ vEq)
        (interp V ρ (ConLeche.Model.AnnotTerm.instSeq zs (zs.length - 1) vα)))
        (interp V ρ (ConLeche.Model.AnnotTerm.instSeq zs (zs.length - 1) vL)))
        (interp V ρ (ConLeche.Model.AnnotTerm.instSeq zs (zs.length - 1) vR))
      = _
    rw [interp_instSeq, interp_instSeq, interp_instSeq, hvEq']
    exact hlaw ρ _ _ _ hαuniv hLmem hRmem
  -- fire: the residual is inhabited, and it is a truth value
  obtain ⟨y, hy⟩ := teleFitPA_nonempty hfit (hstmtInhab ρ)
  rw [hresid] at hy
  exact ⟨vα, vL, vR, hvα, hvL, hvR, mem_eqv hy⟩

/-! ## The certified sides' memberships -/

/-- **The certified sides' memberships, at the reading** (`sidesMemS`):
the recorded `checkIotaSidesTy` runs, converted at the frame's own
context, put both equation sides in the slot — and grade all three.

Where v1 rebuilds three `CtxOkR`s and fires quantified-context packs,
the P tier reads the two runs `IotaRuns` records straight through
`InferClaim`/`DefEqClaim`; the context is the stages' shared
one. -/
theorem sidesMem {m : EnvModel V env} {F : Nat} {ψ' : Name → Nat}
    (hinfer : InferClaim μ m ψ' F) (hclaims : DefEqClaim μ m ψ' F)
    {d : Nat} {Δa : List AnnotTerm} {αS lhsS rhsS : Expr}
    (hctxα : CtxOk m ψ' d Δa αS)
    (hctxL : CtxOk m ψ' d Δa lhsS)
    (hctxR : CtxOk m ψ' d Δa rhsS)
    (hwsα : Expr.WScoped d αS) (hbα : αS.looseBVarsBounded 0 = true)
    (hLα : Expr.LeavesBounded αS)
    (hwsL : Expr.WScoped d lhsS) (hbL : lhsS.looseBVarsBounded 0 = true)
    (hLL : Expr.LeavesBounded lhsS)
    (hwsR : Expr.WScoped d rhsS) (hbR : rhsS.looseBVarsBounded 0 = true)
    (hLR : Expr.LeavesBounded rhsS)
    {vα vL vR : AnnotTerm}
    (hvα : denoteMeta m.acval env ψ' d αS = some vα)
    (hvL : denoteMeta m.acval env ψ' d lhsS = some vL)
    (hvR : denoteMeta m.acval env ψ' d rhsS = some vR)
    -- the slot's own grading (the statement body's, descended)
    (hokα : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ vα)
    {tl tr : Expr}
    (hInfL : inferTypeCore μ env F d lhsS = .ok tl)
    (hDeqL : isDefEqCore μ env F d tl αS = .ok true)
    (hInfR : inferTypeCore μ env F d rhsS = .ok tr)
    (hDeqR : isDefEqCore μ env F d tr αS = .ok true)
    {tla tra : AnnotTerm}
    (htla : denoteMeta m.acval env ψ' d tl = some tla)
    (htra : denoteMeta m.acval env ψ' d tr = some tra)
    (hctxTl : CtxOk m ψ' d Δa tl) (hctxTr : CtxOk m ψ' d Δa tr)
    (hwsTl : Expr.WScoped d tl) (hbTl : tl.looseBVarsBounded 0 = true)
    (hLTl : Expr.LeavesBounded tl)
    (hwsTr : Expr.WScoped d tr) (hbTr : tr.looseBVarsBounded 0 = true)
    (hLTr : Expr.LeavesBounded tr) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ vL) ∧
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ vR) ∧
      ∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ vL ∈ˢ interp V ρ vα ∧
        interp V ρ vR ∈ˢ interp V ρ vα := by
  obtain ⟨hokL, hokTl, hmemL⟩ :=
    hinfer hInfL hwsL hbL hLL hctxL hvL htla
  obtain ⟨hokR, hokTr, hmemR⟩ :=
    hinfer hInfR hwsR hbR hLR hctxR hvR htra
  refine ⟨hokL, hokR, fun ρ hρ => ⟨?_, ?_⟩⟩
  · have heq := hclaims hDeqL hwsTl hbTl hLTl hwsα hbα hLα hctxTl hctxα
      htla hvα hokTl hokα ρ hρ
    exact heq ▸ hmemL ρ hρ
  · have heq := hclaims hDeqR hwsTr hbTr hLTr hwsα hbα hLα hctxTr hctxα
      htra hvα hokTr hokα ρ hρ
    exact heq ▸ hmemR ρ hρ

end ConLeche.Model
