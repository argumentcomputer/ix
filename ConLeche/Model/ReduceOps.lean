module

import ConLeche.Verify.OfReducePin
import ConLeche.Semantics.DeclRun
public import ConLeche.Model.NatEqs
import ConLeche.Model.Capstone
public import ConLeche.Model.ErasePwInv
import ConLeche.Model.DivMod
public section

/-!
# The compiler-trust identity law, established at `interp` from the
recorded certificate run (task #161, ENDGAME D — the pin bundle's
last field)

The ENDGAME C seal named exactly one blocker for `DeclAxiomR`'s
`ofReduce*` branch: the innermost membership obligation is `op a = a`,
which is `EnvS.reduce_ops` (`ReduceOpsV`) — a **v1** field with no
`EnvModelM` mirror, and none derivable (the transfer would be an
erasure factoring of `interp` through `interp`, refuted at the very
λ-nodes the operation's leaf is made of).  `ReduceOps`
(`Annot/EnvModelM.lean`) is that mirror, and this file is its supplier.

## The route: the run-certificate move, fifth execution

`checkReducePin` runs the identity certificate and `ReducePinR`
**records the run** (`SetR/Decl.lean:270`):

> `isDefEqCore μ env F 1 (.app valA (reduceCertVar c)) (reduceCertVar c)
> = .ok true`

— `isDefEq` at depth `1`, applied side first, over the canonical
one-entry element context `reduceCertVar c = .fvar 0 (reduceElemTy c)`.
`DefEqClaim` at the **pre-insertion** environment turns that run
into an `interp` equality of the two sides' readings, and the two
readings are `.app (A ψ) (.bvar 0)` and `.bvar 0`: the law falls out
by `interp_app` and leaf closedness.

This is `NatEqsP.lean`'s species at a one-variable context instead of
two, and the element type is a stored *level-free constant*
(`reduceElemTy c`, whose `reduceElemOk` guard stores it), so the
context kit collapses to `elemA`/`sat_elemCtx` below.

## What the conversion costs: the gradings

`DefEqClaim` compares **graded** readings.  The certificate
variable's side is free (`WellDenotedV` of a `.bvar` is `True`); the
applied side's `WellDenoted` app clause needs the *applied* membership

> `∃ v A' B', interp ρ (A ψ) ∈ˢ piR v A' B' ∧ x ∈ˢ A' ∧
>   (v = 0 → ∀ y ∈ˢ A', B' y ∈ˢ univZero)`

and every part of it is already established at the install:

* the pin fixes the stored type to `.forallE (.const E []) (.const E [])
  mb₀` **on the nose** below the binder meta — both erasures fix a
  `.const` (the `trustCompiler` branch's lesson, reused) — so the
  type's reading is `.pi 0 (pwBit ψ mb₀.pw) (acval E ψ) (acval E ψ)`
  and `interp` of it is a `piR` over the element set;
* the `piR` membership is the constant's own `mem_type` obligation
  (`hmemA`, which `harvestOpaque` proves anyway);
* the `v = 0` fibre clause is the type reading's **`AnnotValid` `pi`
  third component** — `htyOk`'s own content.  So **no bit is needed**:
  the regime datum `mb₀.pw` stays abstract throughout, exactly as the
  literal tier found (`NatEqsP.lean`'s "no bit positivity is ever
  needed"), and the doctrine that bits are never taken from a
  metatheorem is not even approached.

The preservation half is `reduceOps_cons_fresh` (`DivMod.lean`,
beside its `eq_law` sibling — the law mentions two stored leaves, so
it crosses every cons that is neither of them).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-! ## The one-entry element context -/

/-- The element type's leaf at an assignment (the reduce operations'
element inductives — `Nat`, `Bool` — are stored level-free, so the
spelling is the plain assignment). -/
def elemA {env : Env} (m : EnvModel V env) (c : Name)
    (ψ : Name → Nat) : AnnotTerm :=
  m.acval (ConLeche.reduceElemName c) ψ

/-- The certificate's context: one slot, the element type. -/
def elemCtx {env : Env} (m : EnvModel V env) (c : Name)
    (ψ : Name → Nat) : List AnnotTerm :=
  [elemA m c ψ]

/-- One element member satisfies the one-variable context (the leaf
reading collapses by closedness). -/
theorem sat_elemCtx (m : EnvModel V env) {c : Name} {ψ : Name → Nat}
    {ρ : Nat → V} {x : V} (hx : x ∈ˢ interp V ρ (elemA m c ψ)) :
    Sat V (elemCtx m c ψ) (cons x ρ) := by
  intro i Aa hi
  match i with
  | 0 =>
    obtain rfl : elemA m c ψ = Aa := by simpa [elemCtx] using hi
    show x ∈ˢ interp V _ (m.acval (ConLeche.reduceElemName c) ψ)
    rw [acval_interp_closedC m _ ψ _ ρ]
    exact hx

/-! ## The pinned operation type, inverted -/

/-- The element type expression is the element inductive's bare
constant (`Verify/OfReducePin.lean`'s `ofReduce_elemTy` at the
*operation*'s index rather than the axiom's). -/
theorem reduceElemTy_constS (c : Name) :
    ConLeche.reduceElemTy c = .const (ConLeche.reduceElemName c) [] := by
  unfold ConLeche.reduceElemTy ConLeche.reduceElemName
  split <;> simp [ConLeche.natName, ConLeche.boolName]

/-- **The reduce operation's pinned type, inverted through both
erasures.**  The domain and the codomain are the *same* bare constant,
and both erasures fix a `.const`, so the pin leaves exactly the binder
name and the binder meta free — and neither is ever read below. -/
theorem reduceOp_shapeS {c : Name} {type' : Expr}
    (hc : c ∈ ConLeche.reduceOpNames)
    (h : type'.erasePw
      = (ConLeche.reduceOpCvA c).type.erasePw) :
    ∃ mb₀, type' = .forallE (ConLeche.reduceElemTy c)
      (ConLeche.reduceElemTy c) mb₀ := by
  have hcases : c = ConLeche.reduceNatName ∨ c = ConLeche.reduceBoolName := by
    simpa [ConLeche.reduceOpNames] using hc
  have hshape : (ConLeche.reduceOpCvA c).type.erasePw
      = .forallE
          (ConLeche.reduceElemTy c) (ConLeche.reduceElemTy c)
          ⟨.never⟩ := by
    rcases hcases with rfl | rfl <;>
      simp [ConLeche.reduceOpCvA, ConLeche.reduceNatCvA,
        ConLeche.reduceBoolCvA, ConLeche.reduceElemTy, ConLeche.reduceNatName,
        ConLeche.reduceBoolName, ConLeche.natName, ConLeche.boolName,
        Expr.erasePw]
  rw [hshape] at h
  obtain ⟨ty', b', m', rfl, hty', hb'⟩ := erasePwNames_forallE_invS h
  have hE := reduceElemTy_constS c
  rw [hE] at hty' hb'
  obtain rfl := erasePwNames_const_invS hty'
  obtain rfl := erasePwNames_const_invS hb'
  exact ⟨m', by rw [hE]⟩

-- (`reduceElem_sort` in `Verify/OfReducePin.lean` already says the
-- element inductive is stored level-free at `Sort 1`; the earlier
-- draft of this file restated its first two conjuncts and the
-- duplicate was deleted before landing.)

/-! ## The certificate variable's syntactic package -/

/-- The certificate variable's leaf list: one leaf at index `0`, whose
annotation is the element type (a bare constant, so the hereditary
recursion stops there). -/
theorem reduceCertVar_fvarLeaves (c : Name) :
    (ConLeche.reduceCertVar c).fvarLeaves
      = [(0, ConLeche.reduceElemTy c)] := by
  have hE := reduceElemTy_constS c
  simp [ConLeche.reduceCertVar, hE, Expr.fvarLeaves]

/-! ## The establishment -/

/-- **`ReduceOps` at a compiler-trust opaque's own install.**  The
recorded identity-certificate run, converted through `DefEqClaim` at
the pre-insertion environment over the one-entry element context; every
other stored reduce operation crosses by `reduceOps_entry_cons`.  See
the module docstring for the route and for why no regime bit is ever
read. -/
theorem reduceOps_install (hμ : μ.verifiedChecks = true)
    (mp : EnvModelM V μ env) {F : Nat}
    {cv : ConstantVal} {value type' value' : Expr}
    {A Ta : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? cv.name = none)
    (hvf' : value'.hasFvar = false)
    (hbv' : value'.looseBVarsBounded 0 = true)
    (hannv : ConLeche.annotateCore μ env F 0 value = .ok value')
    (hA : ∀ ψ : Name → Nat,
      denoteMeta mp.base2.acval env ψ 0 value' = some (A ψ))
    (hAclosed : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ)
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenoted V ρ (A ψ))
    (hAvalid : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotValid V ρ (A ψ))
    (hTa : ∀ ψ : Name → Nat,
      denoteMeta mp.base2.acval env ψ 0 type' = some (Ta ψ))
    (hTaOk : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (Ta ψ))
    (hmemA : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (A ψ) ∈ˢ interp V ρ (Ta ψ))
    (hred : ConLeche.reduceOpNames.contains cv.name = true →
      ReducePinRun μ F env
        ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts⟩
        cv.name value)
    (m₂ : EnvModel V
      ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval cv.name A) :
    ReduceOps m₂ := by
  intro c hcN cvR hf₂ hpin
  by_cases hne : c = cv.name
  case neg =>
    exact reduceOps_entry_cons mp.reduce_ops
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩) (A := A)
      hfresh m₂ hac hcN hne hf₂ hpin
  subst hne
  -- the recorded certificate, and its annotated subject
  obtain ⟨-, helemOk, -, valA, pinA, hannA, -, hrun⟩ :=
    hred (List.contains_iff_mem.mpr hcN)
  obtain rfl : valA = value' := Except.ok.inj (hannA.symm.trans hannv)
  -- the element inductive is stored, level-free, and is not the cons
  obtain ⟨ciE, hfE, hlpE, -⟩ := ConLeche.Verify.reduceElem_sort helemOk
  have hneE : ConLeche.reduceElemName cv.name ≠ cv.name := by
    intro h; rw [h, hfresh] at hfE; exact nomatch hfE
  have hEty := reduceElemTy_constS cv.name
  have hdenE : ∀ (ψ : Name → Nat) (d : Nat),
      denoteMeta mp.base2.acval env ψ d (ConLeche.reduceElemTy cv.name)
        = some (mp.base2.acval (ConLeche.reduceElemName cv.name) ψ) := by
    intro ψ d
    rw [hEty]
    exact denoteMeta_levelless_const hfE hlpE
  -- the two leaf moves
  have hmoveE : m₂.acval (ConLeche.reduceElemName cv.name)
      = mp.base2.acval (ConLeche.reduceElemName cv.name) := by
    rw [hac]; exact acvalWith_ne hneE
  have hmoveC : m₂.acval cv.name = A := by
    rw [hac]; exact acvalWith_self
  -- `A` is a leaf, hence environment-blind
  have hclA : ∀ ρ₁ ρ₂ : Nat → V, ∀ ψ : Name → Nat,
      interp V ρ₁ (A ψ) = interp V ρ₂ (A ψ) := by
    intro ρ₁ ρ₂ ψ
    have h := acval_interp_closedC m₂ cv.name ψ ρ₁ ρ₂
    rwa [hmoveC] at h
  -- the stored entry is the pinned type, and the pin fixes its shape
  rw [ConLeche.Env.find?_cons, if_pos (show (ConstantInfo.axiomInfo
    ⟨cv.name, cv.levelParams, type'⟩).name = cv.name from rfl)] at hf₂
  obtain rfl : cvR = ⟨cv.name, cv.levelParams, type'⟩ :=
    (ConstantInfo.axiomInfo.inj (Option.some.inj hf₂)).symm
  simp only [ConstantVal.matchesPin, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hpin
  obtain ⟨mb₀, htyShape⟩ := reduceOp_shapeS hcN hpin.2
  subst htyShape
  -- the type's reading: a one-step `.pi` over the element leaf
  have hinst : (ConLeche.reduceElemTy cv.name).instantiate1
        (.fvar 0 (ConLeche.reduceElemTy cv.name))
      = ConLeche.reduceElemTy cv.name :=
    Expr.instantiate1_eq_self (by rw [hEty]; rfl)
  have hTaShape : ∀ ψ : Name → Nat,
      Ta ψ = .pi 0 (pwBit ψ mb₀.pw)
        (mp.base2.acval (ConLeche.reduceElemName cv.name) ψ)
        (mp.base2.acval (ConLeche.reduceElemName cv.name) ψ) := by
    intro ψ
    have h := hTa ψ
    rw [show denoteMeta mp.base2.acval env ψ 0
          (Expr.forallE (ConLeche.reduceElemTy cv.name)
            (ConLeche.reduceElemTy cv.name) mb₀)
        = some (.pi 0 (pwBit ψ mb₀.pw)
            (mp.base2.acval (ConLeche.reduceElemName cv.name) ψ)
            (mp.base2.acval (ConLeche.reduceElemName cv.name) ψ)) from by
      rw [denoteMeta_forallE, hdenE ψ 0, hinst, hdenE ψ 1]; rfl] at h
    exact (Option.some.inj h).symm
  -- the certificate variable's syntactic and context packages
  have hvLeaves : valA.fvarLeaves = [] :=
    Expr.fvarLeaves_eq_nil_of_not_hasFvar hvf'
  have hcertLeaves := reduceCertVar_fvarLeaves cv.name
  have hwsV : ∀ d : Nat, Expr.WScoped d valA :=
    fun d => Expr.WScoped.of_not_hasFvar hvf'
  have hwsCert : Expr.WScoped 1 (ConLeche.reduceCertVar cv.name) := by
    rw [ConLeche.reduceCertVar, hEty]
    simp [Expr.WScoped]
  have hbCert : (ConLeche.reduceCertVar cv.name).looseBVarsBounded 0 = true := by
    rw [ConLeche.reduceCertVar]; rfl
  have hLCert : Expr.LeavesBounded (ConLeche.reduceCertVar cv.name) := by
    intro l hl
    rw [hcertLeaves] at hl
    obtain rfl : l = (0, ConLeche.reduceElemTy cv.name) := by simpa using hl
    rw [hEty]; rfl
  have hwsApp : Expr.WScoped 1
      (Expr.app valA (ConLeche.reduceCertVar cv.name)) := by
    rw [Expr.WScoped]
    exact ⟨hwsV 1, hwsCert⟩
  have hbApp : Expr.looseBVarsBounded 0
      (Expr.app valA (ConLeche.reduceCertVar cv.name)) = true := by
    rw [show Expr.looseBVarsBounded 0
        (Expr.app valA (ConLeche.reduceCertVar cv.name))
      = (Expr.looseBVarsBounded 0 valA &&
          Expr.looseBVarsBounded 0 (ConLeche.reduceCertVar cv.name))
      from rfl, hbv', hbCert]
    rfl
  have hLApp : Expr.LeavesBounded
      (Expr.app valA (ConLeche.reduceCertVar cv.name)) := by
    intro l hl
    rw [show (Expr.app valA (ConLeche.reduceCertVar cv.name)).fvarLeaves
        = valA.fvarLeaves ++ (ConLeche.reduceCertVar cv.name).fvarLeaves
        from by rw [Expr.fvarLeaves], hvLeaves, List.nil_append] at hl
    exact hLCert l hl
  have hctxCert : ∀ ψ : Name → Nat,
      CtxOk mp.base2 ψ 1 (elemCtx mp.base2 cv.name ψ)
        (ConLeche.reduceCertVar cv.name) := by
    intro ψ
    refine ⟨rfl, fun l hl => ?_⟩
    rw [hcertLeaves] at hl
    obtain rfl : l = (0, ConLeche.reduceElemTy cv.name) := by simpa using hl
    refine ⟨Nat.zero_lt_one, by rw [hEty]; trivial,
      mp.base2.acval (ConLeche.reduceElemName cv.name) ψ,
      elemA mp.base2 cv.name ψ, hdenE ψ 1, rfl, fun ρ' _ => ?_,
      fun ρ' _ => ⟨mp.base2.acval_wellDenoted _ ψ ρ', mp.acval_validV _ ψ ρ'⟩⟩
    exact acval_interp_closedC mp.base2 _ ψ _ _
  have hctxApp : ∀ ψ : Name → Nat,
      CtxOk mp.base2 ψ 1 (elemCtx mp.base2 cv.name ψ)
        (Expr.app valA (ConLeche.reduceCertVar cv.name)) := by
    intro ψ
    refine ⟨rfl, fun l hl => ?_⟩
    rw [show (Expr.app valA (ConLeche.reduceCertVar cv.name)).fvarLeaves
        = valA.fvarLeaves ++ (ConLeche.reduceCertVar cv.name).fvarLeaves
        from by rw [Expr.fvarLeaves], hvLeaves, List.nil_append] at hl
    exact (hctxCert ψ).2 l hl
  -- the two sides' readings at the certificate's depth
  have hdenCert : ∀ ψ : Name → Nat,
      denoteMeta mp.base2.acval env ψ 1 (ConLeche.reduceCertVar cv.name)
        = some (.bvar 0) := by
    intro ψ
    rw [ConLeche.reduceCertVar, denoteMeta_fvar]
  have hdenV1 : ∀ ψ : Name → Nat,
      denoteMeta mp.base2.acval env ψ 1 valA = some (A ψ) := fun ψ =>
    denoteMeta_depth_of_closed mp.base2.acval_closed hvf'
      (fun k => hAclosed ψ k) (hA ψ) 1
  have hdenApp : ∀ ψ : Name → Nat,
      denoteMeta mp.base2.acval env ψ 1
          (Expr.app valA (ConLeche.reduceCertVar cv.name))
        = some (.app (A ψ) (.bvar 0)) := by
    intro ψ
    rw [denoteMeta_app, hdenV1 ψ, hdenCert ψ]
    rfl
  -- the claims at the prefix environment
  have hclaims := fun ψ =>
    checkSoundAt (V := V) hμ (Rules.RulesInputs.ofSem mp ψ) F
  refine ⟨?_, fun ψ ρ x hx => ?_⟩
  · rw [ConLeche.Env.find?_cons, if_neg (fun h => hneE h.symm), hfE]; rfl
  obtain ⟨-, -, ihd, -⟩ := hclaims ψ
  rw [hmoveE] at hx
  rw [hmoveC]
  -- the certificate variable's slot membership, at any satisfying `ρ'`
  have hslot : ∀ ρ' : Nat → V, Sat V (elemCtx mp.base2 cv.name ψ) ρ' →
      ρ' 0 ∈ˢ interp V ρ' (mp.base2.acval (ConLeche.reduceElemName cv.name) ψ) := by
    intro ρ' hsat
    have h : ρ' 0 ∈ˢ interp V (fun j => ρ' (j + 0 + 1))
        (mp.base2.acval (ConLeche.reduceElemName cv.name) ψ) :=
      hsat 0 (elemA mp.base2 cv.name ψ) rfl
    rwa [acval_interp_closedC mp.base2 _ ψ _ ρ'] at h
  -- the gradings: the bare variable is free, the applied side is the
  -- constant's own `mem_type`/`type_wellDenotedV` content
  have hgradeCert : ∀ ρ' : Nat → V, Sat V (elemCtx mp.base2 cv.name ψ) ρ' →
      WellDenotedV V ρ' (.bvar 0) := by
    intro ρ' _
    exact ⟨by simp, by simp⟩
  have hgradeApp : ∀ ρ' : Nat → V, Sat V (elemCtx mp.base2 cv.name ψ) ρ' →
      WellDenotedV V ρ' (.app (A ψ) (.bvar 0)) := by
    intro ρ' hsat
    have hfib : (fun y => interp V (cons y ρ')
          (mp.base2.acval (ConLeche.reduceElemName cv.name) ψ))
        = fun _ : V => interp V ρ'
            (mp.base2.acval (ConLeche.reduceElemName cv.name) ψ) :=
      funext fun y => acval_interp_closedC mp.base2 _ ψ _ ρ'
    have hm := hmemA ψ ρ'
    rw [hTaShape ψ, interp_pi, hfib] at hm
    have hv := (hTaOk ψ ρ').2
    rw [hTaShape ψ, AnnotValid_pi] at hv
    refine ⟨⟨hAok ψ ρ', by simp, ?_⟩, ⟨hAvalid ψ ρ', by simp⟩⟩
    refine ⟨pwBit ψ mb₀.pw,
      interp V ρ' (mp.base2.acval (ConLeche.reduceElemName cv.name) ψ),
      fun _ => interp V ρ'
        (mp.base2.acval (ConLeche.reduceElemName cv.name) ψ),
      hm, hslot ρ' hsat, fun h0 y hy => ?_⟩
    have := hv.2.2 h0 y hy
    rwa [acval_interp_closedC mp.base2 _ ψ _ ρ'] at this
  -- the run, converted
  have heq := ihd (d := 1)
    (a := Expr.app valA (ConLeche.reduceCertVar cv.name))
    (b := ConLeche.reduceCertVar cv.name) (Δa := elemCtx mp.base2 cv.name ψ)
    hrun hwsApp hbApp hLApp hwsCert hbCert hLCert
    (hctxApp ψ) (hctxCert ψ) (hdenApp ψ) (hdenCert ψ)
    hgradeApp hgradeCert (cons x ρ) (sat_elemCtx mp.base2 hx)
  rw [interp_app, interp_bvar] at heq
  show SetTheory.app (interp V ρ (A ψ)) x = x
  rw [hclA ρ (cons x ρ) ψ]
  exact heq

end ConLeche.Model
