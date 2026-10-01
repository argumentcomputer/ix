module

import ConLeche.Semantics.IndBlockRun
public import ConLeche.Model.IotaRulePlain
import ConLeche.Model.IndPinRow
import ConLeche.Model.IndBottomNested
import ConLeche.Model.Annot.BitLevels
import ConLeche.Verify.Denote.OpenRevDenote
public section

/-!
# The per-rule bridge, nested branch (task #161, IND TIER part 9)

`iotaRuleS`'s transpose on the `.nested` branch: one checked
nested-auxiliary rule kit yields its `RecRuleLaw` row, by firing
`indBottomNested` for the law's *equality* half and `nestedPinRow`
for the conjunct the P tier's repair added.

**What is new against the canonical branch** is exactly the repaired
conjunct, and it is produced here rather than by the bottom for the
reason part 6 recorded: it is an OUTER conjunct (the consumer feeds it
to `DefEqClaim` to produce the equality clause the inner block
consumes, so inner placement is circular).  Its three suppliers are
`nestedPinRow`'s (`Interp/IndPinRowP.lean`), and the one step this
file adds is the **level crossing**: `RecRuleLaw` states the conjunct
at the ambient `φ` on the `us`-instantiated pin, the row produces it
at `Level.substFn φ lps us` on the stored pin, and
`openRev_instantiateLevelParams` + `denotePInstLevels` identify the
two.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche.Semantics ConLeche.SetModel

open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  BinderMeta RecRule isDefEqCore inferTypeCore DefEqListOk TypedListOk)

universe w

variable {V : Type w} [SetTheory V]

/-- **One checked `.nested` rule's fired law, at the reading**
(`iotaRuleS`'s nested branch, plus the P tier's pin conjunct). -/

theorem iotaRuleNested {μ : CheckMode} {F : Nat} {env₂ envSelf : Env}
    (mp : EnvModelM V μ envSelf)
    (hdeq : ∀ ψ : Name → Nat, DefEqClaim μ mp.base2 ψ F)
    (hinf : ∀ ψ : Name → Nat, InferClaim μ mp.base2 ψ F)
    (hreadsP : ∀ ψ : Name → Nat, InferReads mp.base2 μ ψ F)
    {blockNames : List Name} {f : Name → Name}
    (hf : f = fun n =>
      if blockNames.contains n then n.str "_model" else n)
    (hroT : RenameOk mp.base2.acval envSelf f)
    (hIS : BlockInstalledTT blockNames envSelf mp.base2.cvalE)
    (hup : ∀ (n : Name) (ci : ConstantInfo), env₂.find? n = some ci →
      envSelf.find? n = some ci ∨
      ∃ cv mI' rP' rules rules',
        ci = .recInfo cv mI' rP' rules ∧
        envSelf.find? n = some (.recInfo cv mI' rP' rules'))
    {cvA : ConstantVal} {mI rP j : Nat} {r r' : RecRule}
    (hbnA : blockNames.contains cvA.name = true)
    (hself : envSelf.find? cvA.name = some (.recInfo cvA mI rP []))
    (heqfind : env₂.find? eqName = some eqA)
    (hkit : IotaRuleRun μ F env₂ envSelf f cvA.name
      cvA.levelParams cvA.type mI rP j r r')
    {lvls : List Level} {pins : List Expr}
    (hfireN : RecRule.fire r' = .nested lvls pins) (φ : Name → Nat) :
    RecRuleLaw mp.base2 φ cvA.name cvA mI rP r' := by
  obtain ⟨cvjK, cnPK, cnFK, rhsA, hfcK, hnfK, hrb, hrf, hann, hrlp,
    -- `-` at position 13: `IotaRuleR`'s rule-rhs **derivation** row,
    -- no longer consumed (task #161 S10)
    hrres, hstripRhs, hrun0, fire, hr'eq, hbranch⟩ := hkit
  -- the rule's stored shape
  have hr'rhs : RecRule.rhs r' = rhsA := by rw [hr'eq]; rfl
  have hr'ctor : RecRule.ctor r' = RecRule.ctor r := by rw [hr'eq]; rfl
  have hr'cp : RecRule.ctorParams r' = cnPK := by rw [hr'eq]; rfl
  have hr'nf : RecRule.nfields r' = cnFK := by rw [hr'eq, hnfK]; rfl
  have hr'fire : RecRule.fire r' = fire := by rw [hr'eq]; rfl
  -- the recursor's and the constructor's stored guards
  obtain ⟨htyw0, -, -, htyb0, -, -, -⟩ :=
    mp.base2.wf _ (Env.find?_mem hself)
  have htyw : cvA.type.hasFvar = false := htyw0
  have htyb : cvA.type.looseBVarsBounded 0 = true := htyb0
  have hfcS : envSelf.find? (RecRule.ctor r)
      = some (.ctorInfo cvjK cnPK cnFK) := by
    rcases hup _ _ hfcK with h |
      ⟨cv, mI', rP', rules, rules', heq, -⟩
    · exact h
    · exact nomatch heq
  obtain ⟨hCw, hClp, -, hCb, -, -, -⟩ :=
    mp.base2.wf _ (Env.find?_mem hfcS)
  -- the recursor's model counterpart
  obtain ⟨cvm, mval, hm, hfm, hlpsm, -, -⟩ :=
    hIS cvA.name hbnA _ hself
  have hfRnE : envSelf.find? (f cvA.name)
      = some (.defnInfo cvm mval hm) := by
    rw [hf]
    dsimp only
    rw [if_pos hbnA]
    exact hfm
  obtain ⟨ciCm, hfCmE, hCmlps⟩ : ∃ ciCm,
      envSelf.find? (f (RecRule.ctor r)) = some ciCm ∧
      ciCm.toConstantVal.levelParams = cvjK.levelParams := by
    by_cases hbc : blockNames.contains (RecRule.ctor r) = true
    · obtain ⟨cvmC, mvalC, hmC, hfmC, hlpsC, -, -⟩ := hIS _ hbc _ hfcS
      refine ⟨.defnInfo cvmC mvalC hmC, ?_, hlpsC⟩
      rw [hf]
      dsimp only
      rw [if_pos hbc]
      exact hfmC
    · refine ⟨.ctorInfo cvjK cnPK cnFK, ?_, rfl⟩
      rw [hf]
      dsimp only
      rw [if_neg hbc]
      exact hfcS
  have heqfS : envSelf.find? eqName = some eqA := by
    rcases hup _ _ heqfind with h |
      ⟨cv, mI', rP', rules, rules', heq, -⟩
    · exact h
    · exact nomatch heq
  obtain ⟨hrhsAw, hrhsAb⟩ := annotate_syntax hann hrf hrb
  have hRmlps : (ConstantInfo.defnInfo cvm mval
      hm).toConstantVal.levelParams = cvA.levelParams := hlpsm
  have htyOk : ∀ (ψ : Name → Nat) (ta : AnnotTerm),
      denoteMeta mp.base2.acval envSelf ψ 0 cvA.type = some ta →
      ∀ ρ : Nat → V, WellDenotedV V ρ ta :=
    mp.type_wellDenotedV _ (Env.find?_mem hself)
  -- the rule rhs's front door (the H1 exposure; see `iotaRulePlain`)
  have hrhsLeafNil : ∀ l ∈ rhsA.fvarLeaves, False := by
    intro l hl
    rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hrhsAw] at hl
    exact nomatch hl
  have hrhsWs : Expr.WScoped 0 rhsA := Expr.WScoped.of_not_hasFvar hrhsAw
  have hrhsLb : Expr.LeavesBounded rhsA :=
    fun l hl => absurd hl (fun h => hrhsLeafNil l h)
  obtain ⟨t', hrun⟩ := hrun0
  have hrhsKey : ∀ ψ : Name → Nat, ∃ Ra ta,
      denoteMeta mp.base2.acval envSelf ψ 0 rhsA = some Ra ∧
      ∀ ρ : Nat → V, WellDenotedV V ρ Ra ∧
        interp V ρ Ra ∈ˢ interp V ρ ta := by
    intro ψ
    -- the reading, from the RUN (task #161 S10; see `iotaRulePlain`)
    obtain ⟨Ra, hRa⟩ :=
      acceptedReads_of mp.base2 ψ hrun hrhsWs hrhsAb hrhsLb
    have hctx : CtxOk mp.base2 ψ 0 [] rhsA :=
      ⟨rfl, fun l hl => absurd hl (fun h => hrhsLeafNil l h)⟩
    obtain ⟨ta, hta⟩ := hreadsP ψ hrun hrhsWs hrhsAb hrhsLb
      hctx hRa
    obtain ⟨hokRa, -, hmemRa⟩ :=
      hinf ψ hrun hrhsWs hrhsAb hrhsLb hctx hRa hta
    exact ⟨Ra, ta, hRa, fun ρ =>
      ⟨hokRa ρ (Sat_nil V ρ), hmemRa ρ (Sat_nil V ρ)⟩⟩
  have hctorId : ∀ {cvj' : ConstantVal} {cnP' cnF' : Nat},
      envSelf.find? (RecRule.ctor r')
        = some (.ctorInfo cvj' cnP' cnF') →
      cvj' = cvjK ∧ cnP' = cnPK ∧ cnF' = cnFK := by
    intro cvj' cnP' cnF' hf'
    rw [hr'ctor, hfcS] at hf'
    injection hf' with h1
    injection h1 with e1 e2 e3
    exact ⟨e1.symm, e2.symm, e3.symm⟩
  -- ===== the nested branch =====
  obtain ⟨hshape, hthmN⟩ :
      nestedRuleShape env₂ envSelf cvA.name cvA.levelParams cvA.type
          mI rP cnPK j = some (lvls, pins) ∧
        _ := by
    rcases hbranch with ⟨hpl, hfireP0, -⟩ | ⟨hnpl, hrest⟩
    · exfalso
      rw [hr'fire, hfireP0] at hfireN
      exact nomatch hfireN
    · rcases hrest with ⟨hfireI, -⟩ | ⟨lvls0, pins0, hfireN0, hthm0⟩
      · exfalso
        rw [hr'fire, hfireI] at hfireN
        exact nomatch hfireN
      · obtain ⟨rfl, rfl⟩ : lvls0 = lvls ∧ pins0 = pins := by
          rw [hr'fire, hfireN0] at hfireN
          injection hfireN with a b
          exact ⟨a, b⟩
        exact hthm0
  obtain ⟨hrPmI, -, hpinsWf0, -⟩ := nestedRuleShape_inv hshape
  obtain ⟨-, -, -, pre, domD, bodyD, bmD, D,
    -, -, -, hpinsLen⟩ := nestedRuleShape_inv hshape
  have hpinsWf : ∀ p ∈ pins, p.hasFvar = false ∧
      p.looseBVarsBounded rP = true :=
    fun p hp => ⟨(hpinsWf0 p hp).1, (hpinsWf0 p hp).2.2.2⟩
  refine ⟨hrPmI, ?_⟩
  intro us huslen
  -- unpack the nested `iota_j` kit
  obtain ⟨cvt, fvs, tbody, hcvtE, hcvtlps, hopen, hEqH,
    hlen3, hlhead0, hlarity0, hlpre0, hmaj0, hCstripsHead,
    cdoms, cres, rdoms, lrest, fvsP, crest2, cdomsP, crestP, xFvsP,
    ldoms, hcinst, hclen, hrinst, hopenP,
    ⟨hpinAnn, hcinstP, hopenXP, hldomsAr⟩,
    -- `-` at position 19: `IotaThmNR`'s `TypedListW` walk — the S4
    -- census's ONE consumed derivation row, and the row S5 designed
    -- `IotaNestedPinReadsR` for.  It is no longer consumed either
    -- (task #161 S10): the readings come from `hTypedP`, the run
    -- recorded beside it, through `acceptedReads_of`.
    ldomsL, lrest2, hinstLam, hTypedP, hruns⟩ := hthmN
  -- the statement's stored entry and front doors
  obtain ⟨ciT, hciTS, hciTcv⟩ : ∃ ciT, envSelf.find?
      ((cvA.name.str "_model").str s!"iota_{j}") = some ciT ∧
      ciT.toConstantVal = cvt := by
    unfold Env.findCV? at hcvtE
    rcases h : env₂.find? ((cvA.name.str "_model").str s!"iota_{j}")
      with _ | ci₂
    · rw [h] at hcvtE; exact nomatch hcvtE
    · rw [h] at hcvtE
      have hcv₂ : ci₂.toConstantVal = cvt := Option.some.inj hcvtE
      rcases hup _ _ h with h' |
        ⟨cv, mI', rP', rules, rules', heq, h'⟩
      · exact ⟨ci₂, h', hcv₂⟩
      · exact ⟨.recInfo cv mI' rP' rules', h',
        by rw [← hcv₂, heq]; rfl⟩
  obtain ⟨hSw0, -, -, hSb0, -, -, -⟩ :=
    mp.base2.wf _ (Env.find?_mem hciTS)
  rw [hciTcv] at hSw0 hSb0
  have hSw : cvt.type.hasFvar = false := hSw0
  have hSb : cvt.type.looseBVarsBounded 0 = true := hSb0
  have hthm : ∀ ψ : Name → Nat, ∃ ta,
      denoteMeta mp.base2.acval envSelf ψ 0 cvt.type = some ta ∧
      ∀ ρ : Nat → V, (∃ pv : V, pv ∈ˢ interp V ρ ta) ∧
        WellDenotedV V ρ ta := by
    intro ψ
    obtain ⟨ta, hta0⟩ := mp.type_reads ciT (Env.find?_mem hciTS) ψ
    have hta : denoteMeta mp.base2.acval envSelf ψ 0 cvt.type = some ta := by
      rwa [hciTcv] at hta0
    exact ⟨ta, hta, fun ρ =>
      ⟨⟨_, mp.mem_type ciT (Env.find?_mem hciTS) ψ ta hta0 ρ⟩,
        mp.type_wellDenotedV ciT (Env.find?_mem hciTS) ψ ta hta0 ρ⟩⟩
  -- the equation head and its three arguments
  obtain ⟨ℓA, hheadEq⟩ : ∃ ℓA,
      tbody.getAppFn = .const eqName [ℓA] := by
    unfold isEqHead at hEqH
    split at hEqH
    · next c ℓ heq =>
      exact ⟨ℓ, by rw [heq, eq_of_beq hEqH]⟩
    · exact nomatch hEqH
  obtain ⟨αS, lhsS, rhsS, hargs3⟩ : ∃ αS lhsS rhsS,
      tbody.getAppArgs = [αS, lhsS, rhsS] := by
    rcases h : tbody.getAppArgs with _ | ⟨a, l1⟩
    · rw [h] at hlen3; exact nomatch hlen3
    rcases l1 with _ | ⟨b, l2⟩
    · rw [h] at hlen3; exact nomatch hlen3
    rcases l2 with _ | ⟨c, l3⟩
    · rw [h] at hlen3; exact nomatch hlen3
    rcases l3 with _ | ⟨d, l4⟩
    · exact ⟨a, b, c, rfl⟩
    · rw [h] at hlen3; exact nomatch hlen3
  have hα : tbody.getAppArgs.getD 0 (.bvar 0) = αS := by
    rw [hargs3]; rfl
  have hL : tbody.getAppArgs.getD 1 (.bvar 0) = lhsS := by
    rw [hargs3]; rfl
  have hR : tbody.getAppArgs.getD 2 (.bvar 0) = rhsS := by
    rw [hargs3]; rfl
  simp only [hL] at hlhead0 hlarity0 hlpre0 hmaj0
  simp only [hα, hL, hR] at hruns
  obtain ⟨hdeIdx, hdeFld, hdePre, hdeLam, hdeRhs, hsideL, hsideR⟩ :=
    hruns
  have hCstrips' : ∃ bsC0 cbody0 Dc usc,
      cvjK.type.stripPis (cnPK + cnFK) = some (bsC0, cbody0) ∧
      cbody0.getAppFn = Expr.const Dc usc := by
    obtain ⟨bsC0, cbody0, hstripC0, hheadB⟩ := hCstripsHead
    split at hheadB
    · next n us heq =>
      exact ⟨bsC0, cbody0, n, us, hstripC0, heq⟩
    · exact nomatch hheadB
  -- the stored levels' arity, forced semantically
  obtain ⟨Tst0, hTst0, -⟩ := hthm φ
  have hlvlsLen : lvls.length = cvjK.levelParams.length := by
    rw [← hCmlps]
    exact nestedLvlsLength
      (denoteMeta_erase mp.base2.acval_erase 0 _ hTst0)
      hopen hheadEq hargs3 (eq_of_beq hlhead0) hlarity0 hmaj0 hfCmE
  -- ===== the public frame, at the instantiated valuation =====
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Name → Nat,
      ψ = Level.substFn φ cvA.levelParams us := ⟨_, rfl⟩
  obtain ⟨TV, hTV0R⟩ := mp.type_reads _ (Env.find?_mem hself) ψ
  have hTV0 : denoteMeta mp.base2.acval envSelf ψ 0 cvA.type = some TV :=
    hTV0R
  obtain ⟨ΓP, RP, htowerP, hRPden, hdomsP0A⟩ :=
    openPisAtFvars_denotePTele (acval := mp.base2.acval)
      (env := envSelf) (φ := ψ) rP hopenP hTV0
  have hfvsPlen : fvsP.length = rP := openPisAtFvars_length _ hopenP
  have hshapeP : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x →
      ∃ ty, x = Expr.fvar i ty := by
    intro i x hx
    obtain ⟨ty, hx'⟩ := openPisAtFvars_index _ _ _ hopenP i x hx
    exact ⟨ty, by simpa using hx'⟩
  have hdomsP0 : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x →
      denoteMeta mp.base2.acval envSelf ψ i (Expr.fvarTypeD x)
        = some (ΓP.getD (rP - 1 - i) default) := by
    intro i x hx
    have h := hdomsP0A i x hx
    rwa [Nat.zero_add] at h
  have hwsP := openPisAtFvars_WScoped rP cvA.type 0 hopenP
    (Expr.WScoped.of_not_hasFvar htyw)
  have hwsFvsP : ∀ x ∈ fvsP, Expr.WScoped rP x := by
    intro x hx
    have h := hwsP.1 x hx
    rwa [Nat.zero_add] at h
  have hlbFvsP : ∀ (i : Nat) (ty : Expr),
      Expr.fvar i ty ∈ fvsP → ty.looseBVarsBounded 0 = true :=
    fun i ty hmem =>
      (openPisAtFvars_bounded rP hopenP htyb).2 _ hmem
  have hleafClosedP : ∀ l, (∃ x ∈ fvsP, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2 ∈ fvsP := by
    intro l ⟨x, hx, hl⟩
    rcases openPisAtFvars_leaves _ hopenP l (Or.inr ⟨x, hx, hl⟩) with
      h0 | h0
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar htyw] at h0
      exact nomatch h0
    · exact h0
  have hokTV : ∀ σ : Nat → V, WellDenotedV V σ TV := htyOk ψ TV hTV0
  -- the constructor type at the stored instantiation
  have hctyPw : (cvjK.type.instantiateLevelParams cvjK.levelParams
      lvls).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]
    exact hCw
  have hctyPb : (cvjK.type.instantiateLevelParams cvjK.levelParams
      lvls).looseBVarsBounded 0 = true := by
    rw [Expr.looseBVarsBounded_instantiateLevelParams]
    exact hCb
  obtain ⟨TVjP, hTVjP0R⟩ := mp.type_reads _ (Env.find?_mem hfcS)
    (Level.substFn ψ cvjK.levelParams lvls)
  have hTVjP00 : denoteMeta mp.base2.acval envSelf
      (Level.substFn ψ cvjK.levelParams lvls) 0 cvjK.type
      = some TVjP := hTVjP0R
  have hTVjP0 : denoteMeta mp.base2.acval envSelf ψ 0
      (cvjK.type.instantiateLevelParams cvjK.levelParams lvls)
      = some TVjP := by
    rw [denotePInstLevels]
    exact hTVjP00
  have hTVjPcl : ∀ k : Nat, TVjP.liftN 1 k = TVjP := fun k =>
    denoteMeta_closed mp.base2.acval_erase mp.base2.cval_closed
      hctyPw hctyPb hTVjP0 1 k
  have hTVjP : denoteMeta mp.base2.acval envSelf ψ (rP + cnFK)
      (cvjK.type.instantiateLevelParams cvjK.levelParams lvls)
      = some TVjP :=
    denoteMeta_depth_of_closed mp.base2.acval_closed hctyPw hTVjPcl
      hTVjP0 (rP + cnFK)
  have hokTVjP : ∀ σ : Nat → V, WellDenotedV V σ TVjP :=
    mp.type_wellDenotedV _ (Env.find?_mem hfcS) _ TVjP hTVjP0R
  -- **the pins' instantiated readings, from the RUN** (task #161 S10).
  --
  -- They used to come from `IotaThmNR`'s `TypedListW` walk — the ONE
  -- derivation conjunct S4 measured the P lane consuming, and the row
  -- S5's design note froze `IotaNestedPinReadsR` for.  They do not
  -- have to: `acceptedReads_of` ("whatever `inferTypeCore` accepts,
  -- `denoteMeta` reads", ENDGAME A's totality walk) produces the same
  -- readings from the **recorded run** `hTypedP`, whose per-index
  -- inference verdict `typedListOk_getD` extracts.  The walk is a
  -- fuel induction over the checker's own clauses: no derivation, no
  -- relation, no carrier field.
  --
  -- The syntactic pack the totality walk asks for is
  -- `nestedParamRowP`'s own (`IndNestedParamP.lean`), assembled here
  -- from the openers' three syntactic laws.
  have htkPlen : (fvsP.take rP).length = rP := by
    rw [List.length_take, hfvsPlen]
    omega
  have hbFvsP : ∀ x ∈ fvsP, x.looseBVarsBounded 0 = true := by
    intro x hx
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
    obtain ⟨ty, rfl⟩ := hshapeP q x hq
    rfl
  have hopenerLeafP : ∀ (q0 : Nat) (a : Expr),
      (fvsP.take rP)[q0]? = some a → ∀ l ∈ a.fvarLeaves,
        Expr.fvar l.1 l.2 ∈ fvsP := by
    intro q0 a ha l hl
    have hq0lt : q0 < rP := by
      have := (List.getElem?_eq_some_iff.mp ha).1
      rw [htkPlen] at this
      exact this
    rw [List.getElem?_take_of_lt hq0lt] at ha
    obtain ⟨ty, rfl⟩ := hshapeP q0 a ha
    rw [Expr.fvarLeaves] at hl
    rcases List.mem_cons.mp hl with rfl | hl'
    · exact List.mem_of_getElem? ha
    · refine hleafClosedP l ⟨_, List.mem_of_getElem? ha, ?_⟩
      rw [Expr.fvarLeaves]
      exact List.mem_cons_of_mem _ hl'
  have hpinSyn : ∀ x ∈ pins.map (Expr.instSpine (fvsP.take rP) (rP - 1)),
      Expr.WScoped (rP + cnFK) x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    refine ⟨(instSpine_WScoped (rP - 1)
        (Expr.WScoped.of_not_hasFvar (hpinsWf p hp).1)
        (fun x hx => hwsFvsP x (List.mem_of_mem_take hx))).mono
      (by omega), ?_, ?_⟩
    · have h := instSpine_closed (args := fvsP.take rP) (e := p)
        (fun x hx => hbFvsP x (List.mem_of_mem_take hx))
        (by rw [htkPlen]; exact (hpinsWf p hp).2)
      rwa [htkPlen] at h
    · intro l hl
      rcases fvarLeaves_instSpine (rP - 1) hl with hl' | ⟨x, hx, hlx⟩
      · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar (hpinsWf p hp).1] at hl'
        exact nomatch hl'
      · obtain ⟨q0, hq0⟩ := List.getElem?_of_mem hx
        exact hlbFvsP _ _ (hopenerLeafP q0 x hq0 l hlx)
  have hpinsGetD : ∀ q, q < cnPK →
      (pins.map (Expr.instSpine (fvsP.take rP) (rP - 1))).getD q default
        = Expr.instSpine (fvsP.take rP) (rP - 1) (pins.getD q default) := by
    intro q hq
    rw [List.getD, List.getElem?_map, List.getD]
    rcases hp : pins[q]? with _ | p
    · rw [List.getElem?_eq_none_iff, hpinsLen] at hp; omega
    · rfl
  have hpinMem : ∀ q, q < cnPK →
      Expr.instSpine (fvsP.take rP) (rP - 1) (pins.getD q default)
        ∈ pins.map (Expr.instSpine (fvsP.take rP) (rP - 1)) := by
    intro q hq
    have hp : pins[q]? = some (pins.getD q default) := by
      rw [List.getD]
      rcases hp : pins[q]? with _ | p
      · rw [List.getElem?_eq_none_iff, hpinsLen] at hp; omega
      · rfl
    exact List.mem_map.mpr ⟨_, List.mem_of_getElem? hp, rfl⟩
  have hpinRead : ∀ q, q < cnPK →
      ∃ w, denoteMeta mp.base2.acval envSelf ψ (rP + cnFK)
        (Expr.instSpine (fvsP.take rP) (rP - 1) (pins.getD q default))
        = some w := by
    intro q hq
    obtain ⟨ty, hi, -⟩ := typedListOk_getD hTypedP q
      (by rw [List.length_map, hpinsLen]; exact hq)
    rw [hpinsGetD q hq] at hi
    exact acceptedReads_of mp.base2 ψ hi
      (hpinSyn _ (hpinMem q hq)).1 (hpinSyn _ (hpinMem q hq)).2.1
      (hpinSyn _ (hpinMem q hq)).2.2
  -- ===== the pin conjunct's row =====
  have hrow := nestedPinRow (m := mp.base2) (φ := ψ)
    (hdeq ψ) (hinf ψ) (hreadsP ψ) hfvsPlen hshapeP hwsFvsP
    hleafClosedP hlbFvsP htowerP hokTV hdomsP0 hpinsLen hpinsWf
    hctyPw hctyPb hTVjP hokTVjP hcinstP hTypedP hpinRead
  -- ===== fire the nested bottom =====
  obtain ⟨Ra, hRaden, hokRa, hRalaw⟩ := indBottomNested (V := V) mp
    hdeq hinf hreadsP hroT heqfS htyw htyb htyOk hfRnE hRmlps hfcS
    hfCmE hCmlps hCw hCb hClp hrPmI hlvlsLen hpinsLen hpinsWf
    hrhsAw hrhsAb hrhsKey hSw hSb hthm hopen hheadEq hargs3
    (eq_of_beq hlhead0) hlarity0 (eq_of_beq hlpre0) hmaj0 hCstrips'
    hcinst hclen hrinst hopenP hcinstP hopenXP hinstLam
    hTypedP hdeIdx hdePre hdeFld hdeLam hdeRhs hsideL hsideR
    φ us huslen
  refine ⟨Ra, by rw [hr'rhs]; exact hRaden, hokRa, ?_, ?_⟩
  · -- the pin conjunct, crossed to the ambient valuation
    intro lvls' pins' hn i hi
    obtain ⟨rfl, rfl⟩ : lvls' = lvls ∧ pins' = pins := by
      rw [hfireN] at hn
      injection hn with a b
      exact ⟨a.symm, b.symm⟩
    obtain ⟨vpa, hvp, hgr⟩ := hrow i (by rw [← hr'cp]; exact hi)
    refine ⟨vpa, ?_, ?_⟩
    · rw [openRev_instantiateLevelParams, denotePInstLevels, ← hψ]
      exact hvp
    · intro ρ zs TVa restR hzslen hzsOk hTVa hfit
      obtain rfl : TVa = TV := by
        rw [denotePInstLevels, ← hψ, hTV0] at hTVa
        exact (Option.some.inj hTVa).symm
      exact hgr ρ zs restR hzslen hzsOk hfit
  intro cvj cnP cnF hfcv usj ρ xs ys TVa TVja restR restC hlenX hlenY
    husjlen hlev hplain hnested hidx hTVa hTVja hfitR hfitC
  obtain ⟨rfl, rfl, rfl⟩ := hctorId hfcv
  rw [hr'cp, hr'nf] at hlenY
  rw [hr'cp] at hidx hnested ⊢
  rw [hr'ctor] at hfitR ⊢
  refine hRalaw usj ρ xs ys TVa TVja restR restC hlenX hlenY husjlen
    ?_ ?_ hidx hTVa hTVja hfitR hfitC
  · rw [hlev, recFireComparands_nested hfireN]
  · exact hnested lvls pins hfireN

/-- **The per-rule bridge, at the reading** (`iotaRuleS`): the two
branches, dispatched on the stored fire mode. -/
theorem iotaRule {μ : CheckMode} {F : Nat} {env₂ envSelf : Env}
    (mp : EnvModelM V μ envSelf)
    (hdeq : ∀ ψ : Name → Nat, DefEqClaim μ mp.base2 ψ F)
    (hinf : ∀ ψ : Name → Nat, InferClaim μ mp.base2 ψ F)
    (hreadsP : ∀ ψ : Name → Nat, InferReads mp.base2 μ ψ F)
    {blockNames : List Name} {f : Name → Name}
    (hf : f = fun n =>
      if blockNames.contains n then n.str "_model" else n)
    (hroT : RenameOk mp.base2.acval envSelf f)
    (hIS : BlockInstalledTT blockNames envSelf mp.base2.cvalE)
    (hup : ∀ (n : Name) (ci : ConstantInfo), env₂.find? n = some ci →
      envSelf.find? n = some ci ∨
      ∃ cv mI' rP' rules rules',
        ci = .recInfo cv mI' rP' rules ∧
        envSelf.find? n = some (.recInfo cv mI' rP' rules'))
    {cvA : ConstantVal} {mI rP j : Nat} {r r' : RecRule}
    (hbnA : blockNames.contains cvA.name = true)
    (hself : envSelf.find? cvA.name = some (.recInfo cvA mI rP []))
    (heqfind : env₂.find? eqName = some eqA)
    (hkit : IotaRuleRun μ F env₂ envSelf f cvA.name
      cvA.levelParams cvA.type mI rP j r r')
    (hfire : RecRule.fire r' ≠ .inert) (φ : Name → Nat) :
    RecRuleLaw mp.base2 φ cvA.name cvA mI rP r' := by
  cases hfm : RecRule.fire r' with
  | inert => exact absurd hfm hfire
  | plain =>
    exact iotaRulePlain mp hdeq hinf hreadsP hf hroT hIS hup hbnA
      hself heqfind hkit hfm φ
  | nested lvls pins =>
    exact iotaRuleNested mp hdeq hinf hreadsP hf hroT hIS hup hbnA
      hself heqfind hkit hfm φ

/-- **Every rule the per-recursor fold returns carries its fired law**
(`iotaRulesS`'s P half).  The syntactic clauses of `RuleFactsS` are
V-free and the v1 fold already establishes them; what the P tier owes
is the row. -/

theorem iotaRules {μ : CheckMode} {F : Nat} {env₂ envSelf : Env}
    (mp : EnvModelM V μ envSelf)
    (hdeq : ∀ ψ : Name → Nat, DefEqClaim μ mp.base2 ψ F)
    (hinf : ∀ ψ : Name → Nat, InferClaim μ mp.base2 ψ F)
    (hreadsP : ∀ ψ : Name → Nat, InferReads mp.base2 μ ψ F)
    {blockNames : List Name} {f : Name → Name}
    (hf : f = fun n =>
      if blockNames.contains n then n.str "_model" else n)
    (hroT : RenameOk mp.base2.acval envSelf f)
    (hIS : BlockInstalledTT blockNames envSelf mp.base2.cvalE)
    (hup : FoldUpS env₂ envSelf)
    {cvA : ConstantVal} {mI rP : Nat}
    (hbnA : blockNames.contains cvA.name = true)
    (hself : envSelf.find? cvA.name = some (.recInfo cvA mI rP []))
    (heqfind : env₂.find? eqName = some eqA) :
    ∀ (j : Nat) (rules rules' : List RecRule),
      IotaRulesRun μ F env₂ envSelf f cvA.name
        cvA.levelParams cvA.type mI rP j rules rules' →
      ∀ rl ∈ rules', RecRule.fire rl ≠ .inert → ∀ φ : Name → Nat,
        RecRuleLaw mp.base2 φ cvA.name cvA mI rP rl := by
  intro j rules
  induction rules generalizing j with
  | nil =>
    intro rules' h rl hrl
    rw [h] at hrl
    exact nomatch hrl
  | cons r rest ih =>
    intro rules' h rl hrl
    obtain ⟨r', rest', hkit, hrec, rfl⟩ := h
    rcases List.mem_cons.mp hrl with heqrl | hrl'
    · intro hfire φ
      rw [heqrl] at hfire ⊢
      exact iotaRule mp hdeq hinf hreadsP hf hroT hIS hup hbnA hself
        heqfind hkit hfire φ
    · exact ih (j + 1) rest' hrec rl hrl'

end ConLeche.Model
