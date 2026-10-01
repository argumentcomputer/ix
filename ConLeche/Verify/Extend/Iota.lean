module

public import ConLeche.Verify.Extend.Inversions
public import ConLeche.Verify.IotaWalkInv
import ConLeche.Verify.Shift
public import ConLeche.Verify.Abstract
public import ConLeche.Verify.Subst
public import ConLeche.Verify.EnvWF

public section

/-!
# Iota

The kernel-checked hypothesis kits of modeled recursor rules
(`RuleChecked`, from `checkIotaRules_inv`) and of a block's
capability record (`EtaPins`, from `checkEtaThm_inv` /
`checkUnitThm_inv`).

The whole module is checker inversion over `Env`/`Expr`: no statement
here mentions a valuation, so the semantics and model tiers consume the
kits directly (`ConLeche/Model/IndCaps.lean`,
`ConLeche/Semantics/IndBlockFacts.lean`).
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

variable {mode : CheckMode}

open Expr

/-- The kernel-checked data of a *canonical* rule's `iota_j` theorem:
everything `modeled_rule_fold` consumes.  `env` is the environment the
theorem is stored in, `env₀` the provisional one carrying the block's
rule-less recursors (the definitional-equality checks ran there). -/
@[expose] def PlainChecked (mode : CheckMode) (F : Nat) (env env₀ : Env) (f : Name → Name)
    (cvA : ConstantVal) (mI rP cnP cnF j : Nat) (r : RecRule)
    (cvj : ConstantVal) : Prop :=
  ∃ (thmName : Name) (cvt : ConstantVal) (ci : ConstantInfo)
    (fvs : List Expr) (tbody : Expr) (ℓA : Level) (αS lhsS rhsS : Expr)
    (cdoms : List Expr) (cres : Expr) (rdoms : List Expr) (rrest : Expr)
    (fvsP : List Expr) (restP : Expr) (cdomsP : List Expr)
    (crestP : Expr) (xFvsP : List Expr) (crest2 : Expr)
    (ldoms : List Expr) (lrest : Expr),
    env.find? thmName = some ci ∧
    ci.toConstantVal = cvt ∧
    -- task #148 T6: the name the checker looked the statement up at,
    -- recorded (the proof always knew it; the statement now says so)
    thmName = (cvA.name.str "_model").str s!"iota_{j}" ∧
    cvt.levelParams = cvA.levelParams ∧
    openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tbody) ∧
    tbody.getAppFn = .const eqName [ℓA] ∧
    tbody.getAppArgs = [αS, lhsS, rhsS] ∧
    lhsS.getAppFn = Expr.const (f cvA.name) (cvA.levelParams.map .param) ∧
    lhsS.getAppArgs.length = mI + 1 ∧
    lhsS.getAppArgs.take rP = fvs.take rP ∧
    lhsS.getAppArgs.getLastD (.bvar 0) =
      Expr.mkAppN (.const (f (RecRule.ctor r)) (cvj.levelParams.map .param))
        (fvs.take cnP ++ fvs.drop rP) ∧
    (cvj.type.stripPis (cnP + cnF)).isSome = true ∧
    Expr.instPisAt (fvs.take cnP ++ fvs.drop rP)
      (cvj.type.renameConsts f) = some (cdoms, cres) ∧
    cres.getAppArgs.length = cnP + (mI - rP) ∧
    DefEqListOk mode F env₀ (rP + cnF)
      ((lhsS.getAppArgs.drop rP).take (mI - rP))
      (cres.getAppArgs.drop cnP) ∧
    DefEqListOk mode F env₀ (rP + cnF)
      ((fvs.drop rP).map Expr.fvarTypeD) (cdoms.drop cnP) ∧
    Expr.instPisAt (fvs.take rP) (cvA.type.renameConsts f) =
      some (rdoms, rrest) ∧
    DefEqListOk mode F env₀ (rP + cnF)
      ((fvs.take rP).map Expr.fvarTypeD) rdoms ∧
    openPisAtFvars rP cvA.type 0 = some (fvsP, restP) ∧
    Expr.instPisAt (fvsP.take cnP) cvj.type = some (cdomsP, crestP) ∧
    DefEqListOk mode F env₀ (rP + cnF)
      ((fvsP.take cnP).map Expr.fvarTypeD) cdomsP ∧
    openPisAtFvars cnF crestP rP = some (xFvsP, crest2) ∧
    Expr.instLamsAt (fvsP ++ xFvsP) (RecRule.rhs r) =
      some (ldoms, lrest) ∧
    DefEqListOk mode F env₀ (rP + cnF)
      ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldoms ∧
    isDefEqCore mode env₀ F (rP + cnF) rhsS
      (Expr.mkAppN ((RecRule.rhs r).renameConsts f) fvs) = .ok true ∧
    (∃ tl, inferTypeCore mode env₀ F (rP + cnF) lhsS = .ok tl ∧
      isDefEqCore mode env₀ F (rP + cnF) tl αS = .ok true) ∧
    (∃ tr, inferTypeCore mode env₀ F (rP + cnF) rhsS = .ok tr ∧
      isDefEqCore mode env₀ F (rP + cnF) tr αS = .ok true) ∧
    -- task #146's slot-sort certification is a TT-lane check
    -- (task #147): delivered only at `mode.ttChecks`
    (mode.ttChecks = true →
      ∃ tα, inferTypeCore mode env₀ F (rP + cnF) αS = .ok tα ∧
        isDefEqCore mode env₀ F (rP + cnF) tα (Expr.sort ℓA) = .ok true)

/-- The kernel-checked data of a *nested-auxiliary* rule's `iota_j`
theorem (`checkIotaThmN`): everything `modeled_rule_fold_nested`
consumes.  Mirrors `PlainChecked` with the constructor applied at the
stored level instantiations `lvls` to the stored parameter
instantiations `pins` (rule-prefix context, opened at the statement's
prefix variables) instead of the leading telescope variables; index
premises between the prefix and the major flow through exactly as on
the plain path (the statement's index arguments are pinned against
the constructor residual's canonical tuple). -/
@[expose] def NestedChecked (mode : CheckMode) (F : Nat) (env env₀ : Env) (f : Name → Name)
    (cvA : ConstantVal) (mI rP cnP cnF j : Nat) (r : RecRule)
    (cvj : ConstantVal) (lvls : List Level) (pins : List Expr) : Prop :=
  ∃ (thmName : Name) (cvt : ConstantVal) (ci : ConstantInfo)
    (fvs : List Expr) (tbody : Expr) (ℓA : Level) (αS lhsS rhsS : Expr)
    (cdoms : List Expr) (cres : Expr) (rdoms : List Expr) (rrest : Expr)
    (fvsP : List Expr) (restP : Expr) (cdomsP : List Expr)
    (crestP : Expr) (xFvsP : List Expr) (crest2 : Expr)
    (ldoms : List Expr) (lrest : Expr),
    env.find? thmName = some ci ∧
    ci.toConstantVal = cvt ∧
    -- task #148 T6: the name the checker looked the statement up at,
    -- recorded (the proof always knew it; the statement now says so)
    thmName = (cvA.name.str "_model").str s!"iota_{j}" ∧
    cvt.levelParams = cvA.levelParams ∧
    openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tbody) ∧
    tbody.getAppFn = .const eqName [ℓA] ∧
    tbody.getAppArgs = [αS, lhsS, rhsS] ∧
    lhsS.getAppFn = Expr.const (f cvA.name) (cvA.levelParams.map .param) ∧
    lhsS.getAppArgs.length = mI + 1 ∧
    lhsS.getAppArgs.take rP = fvs.take rP ∧
    Expr.ErasedEq (lhsS.getAppArgs.getLastD (.bvar 0))
      (Expr.mkAppN (.const (f (RecRule.ctor r)) lvls)
        (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
          (p.renameConsts f)) ++ fvs.drop rP)) ∧
    (∃ bsC0 cbody0 Dc usc,
      cvj.type.stripPis (cnP + cnF) = some (bsC0, cbody0) ∧
      cbody0.getAppFn = Expr.const Dc usc) ∧
    Expr.instPisAt
      (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f)) ++ fvs.drop rP)
      ((cvj.type.instantiateLevelParams cvj.levelParams
        lvls).renameConsts f) = some (cdoms, cres) ∧
    cres.getAppArgs.length = cnP + (mI - rP) ∧
    DefEqListOk mode F env₀ (rP + cnF)
      ((lhsS.getAppArgs.drop rP).take (mI - rP))
      (cres.getAppArgs.drop cnP) ∧
    DefEqListOk mode F env₀ (rP + cnF)
      ((fvs.drop rP).map Expr.fvarTypeD) (cdoms.drop cnP) ∧
    Expr.instPisAt (fvs.take rP) (cvA.type.renameConsts f) =
      some (rdoms, rrest) ∧
    DefEqListOk mode F env₀ (rP + cnF)
      ((fvs.take rP).map Expr.fvarTypeD) rdoms ∧
    openPisAtFvars rP cvA.type 0 = some (fvsP, restP) ∧
    AnnotListOk mode F env₀ (rP + cnF)
      (pins.map (fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p)) ∧
    Expr.instPisAt
      (pins.map (fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p))
      (cvj.type.instantiateLevelParams cvj.levelParams lvls) =
      some (cdomsP, crestP) ∧
    TypedListOk mode F env₀ (rP + cnF)
      (pins.map (fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p))
      cdomsP ∧
    openPisAtFvars cnF crestP rP = some (xFvsP, crest2) ∧
    crest2.getAppArgs.length = cnP + (mI - rP) ∧
    Expr.instLamsAt (fvsP ++ xFvsP) (RecRule.rhs r) =
      some (ldoms, lrest) ∧
    DefEqListOk mode F env₀ (rP + cnF)
      ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldoms ∧
    isDefEqCore mode env₀ F (rP + cnF) rhsS
      (Expr.mkAppN ((RecRule.rhs r).renameConsts f) fvs) = .ok true ∧
    (∃ tl, inferTypeCore mode env₀ F (rP + cnF) lhsS = .ok tl ∧
      isDefEqCore mode env₀ F (rP + cnF) tl αS = .ok true) ∧
    (∃ tr, inferTypeCore mode env₀ F (rP + cnF) rhsS = .ok tr ∧
      isDefEqCore mode env₀ F (rP + cnF) tr αS = .ok true) ∧
    -- task #146's slot-sort certification is a TT-lane check
    -- (task #147): delivered only at `mode.ttChecks`
    (mode.ttChecks = true →
      ∃ tα, inferTypeCore mode env₀ F (rP + cnF) αS = .ok tα ∧
        isDefEqCore mode env₀ F (rP + cnF) tα (Expr.sort ℓA) = .ok true)

/-- Invert a successful `checkIotaThm` run (on the rule as returned,
whose `rhs` is the annotated right-hand side). -/
theorem checkIotaThm_inv {env' env₀ : Env} {f : Name → Name}
    {cvA cvj : ConstantVal} {mI rP j cnP cnF : Nat}
    {r : RecRule} {rhsA : Expr} {u : Unit}
    (h : checkIotaThm mode (fueledOps mode F) env' env₀ f cvA.name cvA.levelParams
      cvA.type mI rP j r cvj cnP cnF rhsA = .ok u) :
    PlainChecked mode F env' env₀ f cvA mI rP cnP cnF j
      { r with rhs := rhsA } cvj := by
  simp only [checkIotaThm, checkIotaSidesTy, unwrapOr, Env.findCV?, fueledOps_annotate,
    fueledOps_inferType, fueledOps_isDefEq, fueledOps_ensureSort,
    fueledOps_whnf, Bind.bind, Except.bind, pure, Except.pure] at h
  revert h
  match hfthm : env'.find? ((cvA.name.str "_model").str s!"iota_{j}") with
  | none => intro h; exact nomatch h
  | some ci => ?_
  intro h
  obtain ⟨cvt, hcvt⟩ : ∃ cvt, ci.toConstantVal = cvt := ⟨_, rfl⟩
  simp only [Option.map_some] at h
  rw [hcvt] at h
  try simp only [Except.bind, pure, Except.pure] at h
  try dsimp only at h
  by_cases hlpt : cvt.levelParams = cvA.levelParams
  case neg => rw [if_neg hlpt] at h; exact nomatch h
  rw [if_pos hlpt] at h
  try dsimp only at h
  revert h
  match hopen : openPisAtFvars (rP + cnF) cvt.type 0 with
  | none => intro h; exact nomatch h
  | some (fvs, tbody) => ?_
  intro h
  try simp only [Except.bind, pure, Except.pure] at h
  try dsimp only at h
  by_cases hhead : isEqHead tbody.getAppFn = true
  case neg => rw [if_neg hhead] at h; exact nomatch h
  rw [if_pos hhead] at h
  obtain ⟨ℓA, hheadEq⟩ := isEqHead_inv hhead
  try dsimp only at h
  by_cases hlen3 : tbody.getAppArgs.length = 3
  case neg => rw [if_neg hlen3] at h; exact nomatch h
  rw [if_pos hlen3] at h
  obtain ⟨αS, lhsS, rhsS, hargs3⟩ :
      ∃ αS lhsS rhsS, tbody.getAppArgs = [αS, lhsS, rhsS] := by
    match hta : tbody.getAppArgs with
    | [a, b, c] => exact ⟨a, b, c, rfl⟩
    | [] => rw [hta] at hlen3; exact nomatch hlen3
    | [_] => rw [hta] at hlen3; exact nomatch hlen3
    | [_, _] => rw [hta] at hlen3; exact nomatch hlen3
    | _ :: _ :: _ :: _ :: _ => rw [hta] at hlen3; simp at hlen3
  rw [hargs3] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  by_cases hlhead : (lhsS.getAppFn ==
      Expr.const (f cvA.name) (cvA.levelParams.map .param)) = true
  case neg => rw [if_neg hlhead] at h; exact nomatch h
  rw [if_pos hlhead] at h
  try dsimp only at h
  by_cases hlarity : lhsS.getAppArgs.length = mI + 1
  case neg => rw [if_neg hlarity] at h; exact nomatch h
  rw [if_pos hlarity] at h
  try dsimp only at h
  by_cases hlpre : (lhsS.getAppArgs.take rP ==
      fvs.take rP) = true
  case neg => rw [if_neg hlpre] at h; exact nomatch h
  rw [if_pos hlpre] at h
  try dsimp only at h
  by_cases hmaj : (lhsS.getAppArgs.getLastD (.bvar 0) ==
      Expr.mkAppN (.const (f (RecRule.ctor r)) (cvj.levelParams.map .param))
        (fvs.take cnP ++ fvs.drop rP)) = true
  case neg => rw [if_neg hmaj] at h; exact nomatch h
  rw [if_pos hmaj] at h
  try dsimp only at h
  by_cases hcstrip : (cvj.type.stripPis (cnP + cnF)).isSome = true
  case neg => rw [if_neg hcstrip] at h; exact nomatch h
  rw [if_pos hcstrip] at h
  try dsimp only at h
  revert h
  match hcinst : Expr.instPisAt (fvs.take cnP ++ fvs.drop rP)
      (cvj.type.renameConsts f) with
  | none => intro h; exact nomatch h
  | some (cdoms, cres) => ?_
  intro h
  try simp only [Except.bind, pure, Except.pure] at h
  try dsimp only at h
  by_cases hclen : cres.getAppArgs.length = cnP + (mI - rP)
  case neg => rw [if_neg hclen] at h; exact nomatch h
  rw [if_pos hclen] at h
  try dsimp only at h
  cases hdq1 : checkDefEqList (fueledOps mode F) env₀ (rP + cnF)
      ((lhsS.getAppArgs.drop rP).take (mI - rP))
      (cres.getAppArgs.drop cnP) with
  | error e => rw [hdq1] at h; exact nomatch h
  | ok u1 =>
  rw [hdq1] at h
  try dsimp only at h
  cases hdq2 : checkDefEqList (fueledOps mode F) env₀ (rP + cnF)
      ((fvs.drop rP).map Expr.fvarTypeD)
      (cdoms.drop cnP) with
  | error e => rw [hdq2] at h; exact nomatch h
  | ok u2 =>
  rw [hdq2] at h
  try dsimp only at h
  revert h
  match hrinst : Expr.instPisAt (fvs.take rP)
      (cvA.type.renameConsts f) with
  | none => intro h; exact nomatch h
  | some (rdoms, rrest) => ?_
  intro h
  try simp only [Except.bind, pure, Except.pure] at h
  try dsimp only at h
  cases hdq3 : checkDefEqList (fueledOps mode F) env₀ (rP + cnF)
      ((fvs.take rP).map Expr.fvarTypeD) rdoms with
  | error e => rw [hdq3] at h; exact nomatch h
  | ok u3 =>
  rw [hdq3] at h
  try dsimp only at h
  revert h
  match hopenP : openPisAtFvars rP cvA.type 0 with
  | none => intro h; exact nomatch h
  | some (fvsP, restP) => ?_
  intro h
  try simp only [Except.bind, pure, Except.pure] at h
  try dsimp only at h
  revert h
  match hcinstP : Expr.instPisAt (fvsP.take cnP) cvj.type with
  | none => intro h; exact nomatch h
  | some (cdomsP, crestP) => ?_
  intro h
  try simp only [Except.bind, pure, Except.pure] at h
  try dsimp only at h
  cases hdqP : checkDefEqList (fueledOps mode F) env₀ (rP + cnF)
      ((fvsP.take cnP).map Expr.fvarTypeD) cdomsP with
  | error e => rw [hdqP] at h; exact nomatch h
  | ok uP =>
  rw [hdqP] at h
  try dsimp only at h
  revert h
  match hopenX : openPisAtFvars cnF crestP rP with
  | none => intro h; exact nomatch h
  | some (xFvsP, crest2) => ?_
  intro h
  try simp only [Except.bind, pure, Except.pure] at h
  try dsimp only at h
  revert h
  match hlinst : Expr.instLamsAt (fvsP ++ xFvsP) rhsA with
  | none => intro h; exact nomatch h
  | some (ldoms, lrest) => ?_
  intro h
  try simp only [Except.bind, pure, Except.pure] at h
  try dsimp only at h
  cases hdq4 : checkDefEqList (fueledOps mode F) env₀ (rP + cnF)
      ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldoms with
  | error e => rw [hdq4] at h; exact nomatch h
  | ok u4 =>
  rw [hdq4] at h
  try dsimp only at h
  revert h
  cases hde : isDefEqCore mode env₀ F (rP + cnF) rhsS
      (Expr.mkAppN (rhsA.renameConsts f) fvs) with
  | error e => intro h; exact nomatch h
  | ok v =>
  cases v with
  | false => intro h; simp at h
  | true =>
  intro h
  try simp only [Except.bind, pure, Except.pure] at h
  try dsimp only at h
  revert h
  cases htl : inferTypeCore mode env₀ F (rP + cnF) lhsS with
  | error e => intro h; exact nomatch h
  | ok tl => ?_
  intro h
  try dsimp only at h
  revert h
  cases hdl : isDefEqCore mode env₀ F (rP + cnF) tl αS with
  | error e => intro h; exact nomatch h
  | ok vl =>
  cases vl with
  | false => intro h; simp at h
  | true =>
  intro h
  try simp only [Except.bind, pure, Except.pure] at h
  try dsimp only at h
  revert h
  cases htr : inferTypeCore mode env₀ F (rP + cnF) rhsS with
  | error e => intro h; exact nomatch h
  | ok tr => ?_
  intro h
  try dsimp only at h
  revert h
  cases hdr : isDefEqCore mode env₀ F (rP + cnF) tr αS with
  | error e => intro h; exact nomatch h
  | ok vr =>
  cases vr with
  | false => intro h; simp at h
  | true =>
  intro h
  try simp only [Except.bind, pure, Except.pure] at h
  try dsimp only at h
  -- task #147: the slot-sort certification (task #146) is gated on the
  -- mode; split on the gate first
  cases htt : mode.ttChecks with
  | false =>
    rw [htt] at h
    simp only [Bool.false_eq_true, if_false, pure, Except.pure] at h
    exact ⟨(cvA.name.str "_model").str s!"iota_{j}", cvt, ci, fvs,
      tbody, ℓA, αS, lhsS, rhsS, cdoms, cres, rdoms, rrest, fvsP,
      restP, cdomsP, crestP, xFvsP, crest2, ldoms, lrest,
      hfthm, hcvt, rfl, hlpt, hopen, hheadEq, hargs3, eq_of_beq hlhead, hlarity,
      eq_of_beq hlpre, eq_of_beq hmaj, hcstrip, hcinst, hclen,
      checkDefEqList_inv hdq1, checkDefEqList_inv hdq2, hrinst,
      checkDefEqList_inv hdq3, hopenP, hcinstP,
      checkDefEqList_inv hdqP, hopenX, hlinst,
      checkDefEqList_inv hdq4, hde, ⟨tl, htl, hdl⟩, ⟨tr, htr, hdr⟩,
      fun hc => absurd hc (by simp [htt])⟩
  | true =>
  rw [htt] at h
  simp only [if_true] at h
  revert h
  cases htα : inferTypeCore mode env₀ F (rP + cnF) αS with
  | error e => intro h; exact nomatch h
  | ok tα => ?_
  intro h
  try dsimp only at h
  revert h
  cases hdα : isDefEqCore mode env₀ F (rP + cnF) tα
      (Expr.sort (eqHeadLevel tbody.getAppFn)) with
  | error e => intro h; exact nomatch h
  | ok vα =>
  cases vα with
  | false => intro h; simp at h
  | true =>
  rw [hheadEq] at hdα
  intro h
  exact ⟨(cvA.name.str "_model").str s!"iota_{j}", cvt, ci, fvs,
    tbody, ℓA, αS, lhsS, rhsS, cdoms, cres, rdoms, rrest, fvsP,
    restP, cdomsP, crestP, xFvsP, crest2, ldoms, lrest,
    hfthm, hcvt, rfl, hlpt, hopen, hheadEq, hargs3, eq_of_beq hlhead, hlarity,
    eq_of_beq hlpre, eq_of_beq hmaj, hcstrip, hcinst, hclen,
    checkDefEqList_inv hdq1, checkDefEqList_inv hdq2, hrinst,
    checkDefEqList_inv hdq3, hopenP, hcinstP,
    checkDefEqList_inv hdqP, hopenX, hlinst,
    checkDefEqList_inv hdq4, hde, ⟨tl, htl, hdl⟩, ⟨tr, htr, hdr⟩,
    fun _ => ⟨tα, htα, hdα⟩⟩

/-- Invert a successful `nestedRuleShape` computation into the facts
the stored rule's flag records: the prefix-major offset, the syntactic
well-formedness of the stored instantiations (lowered into the
rule-prefix context), and the recursor-type pin the instantiations
were read off — the major domain applies the family to the
instantiations' liftings past the index binders followed by the index
variables in order. -/
theorem nestedRuleShape_inv {env' envSelf : Env} {cvName : Name}
    {lps : List Name} {tyA : Expr} {mI rP cnP j : Nat}
    {lvls : List Level} {pins : List Expr}
    (h : nestedRuleShape env' envSelf cvName lps tyA mI rP cnP j =
      some (lvls, pins)) :
    rP ≤ mI ∧
    (∀ l ∈ lvls, l.allParamsDefined lps = true) ∧
    (∀ pin ∈ pins, pin.hasFvar = false ∧
      pin.allLevelParamsDefined lps = true ∧
      pin.constsResolve envSelf = true ∧
      pin.looseBVarsBounded rP = true) ∧
    ∃ pre dom body bm D,
      tyA.stripPis mI = some (pre, .forallE dom body bm) ∧
      dom.getAppFn = .const D lvls ∧
      dom.getAppArgs =
        pins.map (Expr.liftLooseBVars (mI - rP) 0) ++
          (List.range (mI - rP)).map
            (fun i => Expr.bvar (mI - rP - 1 - i)) ∧
      pins.length = cnP := by
  simp only [nestedRuleShape] at h
  split at h
  case isFalse => exact nomatch h
  rename_i hcond1
  revert h
  match hstrip : tyA.stripPis mI with
  | none => intro h; exact nomatch h
  | some (pre, .bvar _) => intro h; exact nomatch h
  | some (pre, .fvar _ _) => intro h; exact nomatch h
  | some (pre, .sort _) => intro h; exact nomatch h
  | some (pre, .const _ _) => intro h; exact nomatch h
  | some (pre, .app _ _) => intro h; exact nomatch h
  | some (pre, .lam _ _ _) => intro h; exact nomatch h
  | some (pre, .letE _ _ _) => intro h; exact nomatch h
  | some (pre, .lit _) => intro h; exact nomatch h
  | some (pre, .proj _ _ _) => intro h; exact nomatch h
  | some (pre, .forallE dom body bm) => ?_
  intro h
  try dsimp only at h
  revert h
  match hfn : dom.getAppFn with
  | .bvar _ => intro h; exact nomatch h
  | .fvar _ _ => intro h; exact nomatch h
  | .sort _ => intro h; exact nomatch h
  | .app _ _ => intro h; exact nomatch h
  | .lam _ _ _ => intro h; exact nomatch h
  | .forallE _ _ _ => intro h; exact nomatch h
  | .letE _ _ _ => intro h; exact nomatch h
  | .lit _ => intro h; exact nomatch h
  | .proj _ _ _ => intro h; exact nomatch h
  | .const D lvls' => ?_
  intro h
  try dsimp only at h
  split at h
  case isFalse => exact nomatch h
  rename_i hcond2
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hlen, htake, hdrop, hpinsAll, hlvlsAll⟩ := hcond2
  have hplen : ((dom.getAppArgs.take cnP).map
      (Expr.lowerBVars (mI - rP) 0)).length = cnP := by
    rw [List.length_map, List.length_take, hlen]
    omega
  refine ⟨hcond1.2, ?_, ?_, pre, dom, body, bm, D, rfl, hfn,
    ?_, hplen⟩
  · intro l hl
    exact List.all_eq_true.mp hlvlsAll l hl
  · intro p hp
    have hall := List.all_eq_true.mp hpinsAll p hp
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hall
    exact ⟨hall.1.1.1, hall.2, hall.1.2, hall.1.1.2⟩
  · conv => lhs; rw [← List.take_append_drop cnP dom.getAppArgs]
    congr 1
    · exact eq_of_beq htake
    · exact eq_of_beq hdrop

/-- Invert a `checkIotaThmN` run (on the rule as returned, whose `rhs`
is the annotated right-hand side): either the rule was stored inert,
or the returned flag carries the certified shape and the full
`NestedChecked` hypothesis kit. -/
theorem checkIotaThmN_inv {env' env₀ : Env} {f : Name → Name}
    {cvA cvj : ConstantVal} {mI rP j cnP cnF : Nat}
    {r : RecRule} {rhsA : Expr} {fire : RecRuleFire}
    (h : checkIotaThmN mode (fueledOps mode F) env' env₀ f cvA.name cvA.levelParams
      cvA.type mI rP j r cvj cnP cnF rhsA = .ok fire) :
    (fire = .inert ∧
      nestedRuleShape env' env₀ cvA.name cvA.levelParams cvA.type
        mI rP cnP j = none) ∨
    ∃ lvls pins, fire = .nested lvls pins ∧
      nestedRuleShape env' env₀ cvA.name cvA.levelParams cvA.type
        mI rP cnP j = some (lvls, pins) ∧
      NestedChecked mode F env' env₀ f cvA mI rP cnP cnF j
        { r with rhs := rhsA } cvj lvls pins := by
  simp only [checkIotaThmN, checkIotaSidesTy] at h
  revert h
  cases hshape : nestedRuleShape env' env₀ cvA.name cvA.levelParams
      cvA.type mI rP cnP j with
  | none =>
    intro h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl ⟨h.symm, rfl⟩
  | some q => ?_
  obtain ⟨lvls, pins⟩ := q
  intro h
  simp only [unwrapOr, Env.findCV?, fueledOps_annotate,
    fueledOps_inferType, fueledOps_isDefEq, fueledOps_ensureSort,
    fueledOps_whnf, Bind.bind, Except.bind, pure, Except.pure] at h
  revert h
  match hfthm : env'.find? ((cvA.name.str "_model").str s!"iota_{j}") with
  | none => intro h; exact nomatch h
  | some ci => ?_
  intro h
  obtain ⟨cvt, hcvt⟩ : ∃ cvt, ci.toConstantVal = cvt := ⟨_, rfl⟩
  simp only [Option.map_some] at h
  rw [hcvt] at h
  try simp only [Except.bind, pure, Except.pure] at h
  try dsimp only at h
  by_cases hlpt : cvt.levelParams = cvA.levelParams
  case neg => rw [if_neg hlpt] at h; exact nomatch h
  rw [if_pos hlpt] at h
  try dsimp only at h
  revert h
  match hopen : openPisAtFvars (rP + cnF) cvt.type 0 with
  | none => intro h; exact nomatch h
  | some (fvs, tbody) => ?_
  intro h
  try simp only [Except.bind, pure, Except.pure] at h
  try dsimp only at h
  by_cases hhead : isEqHead tbody.getAppFn = true
  case neg => rw [if_neg hhead] at h; exact nomatch h
  rw [if_pos hhead] at h
  obtain ⟨ℓA, hheadEq⟩ := isEqHead_inv hhead
  try dsimp only at h
  by_cases hlen3 : tbody.getAppArgs.length = 3
  case neg => rw [if_neg hlen3] at h; exact nomatch h
  rw [if_pos hlen3] at h
  obtain ⟨αS, lhsS, rhsS, hargs3⟩ :
      ∃ αS lhsS rhsS, tbody.getAppArgs = [αS, lhsS, rhsS] := by
    match hta : tbody.getAppArgs with
    | [a, b, c] => exact ⟨a, b, c, rfl⟩
    | [] => rw [hta] at hlen3; exact nomatch hlen3
    | [_] => rw [hta] at hlen3; exact nomatch hlen3
    | [_, _] => rw [hta] at hlen3; exact nomatch hlen3
    | _ :: _ :: _ :: _ :: _ => rw [hta] at hlen3; simp at hlen3
  rw [hargs3] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  by_cases hlhead : (lhsS.getAppFn ==
      Expr.const (f cvA.name) (cvA.levelParams.map .param)) = true
  case neg => rw [if_neg hlhead] at h; exact nomatch h
  rw [if_pos hlhead] at h
  try dsimp only at h
  by_cases hlarity : lhsS.getAppArgs.length = mI + 1
  case neg => rw [if_neg hlarity] at h; exact nomatch h
  rw [if_pos hlarity] at h
  try dsimp only at h
  by_cases hlpre : (lhsS.getAppArgs.take rP ==
      fvs.take rP) = true
  case neg => rw [if_neg hlpre] at h; exact nomatch h
  rw [if_pos hlpre] at h
  try dsimp only at h
  by_cases hmaj : ((lhsS.getAppArgs.getLastD (.bvar 0))
    == (Expr.mkAppN (.const (f (RecRule.ctor r)) lvls)
      (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f)) ++ fvs.drop rP))) = true
  case neg => rw [if_neg hmaj] at h; exact nomatch h
  rw [if_pos hmaj] at h
  try dsimp only at h
  revert h
  match hcstrip : cvj.type.stripPis (cnP + cnF) with
  | none => intro h; exact nomatch h
  | some (bsC0, cbody0) => ?_
  intro h
  try simp only [Except.bind, pure, Except.pure] at h
  try dsimp only at h
  revert h
  match hcheadEq : cbody0.getAppFn with
  | .bvar _ => intro h; exact nomatch h
  | .fvar _ _ => intro h; exact nomatch h
  | .sort _ => intro h; exact nomatch h
  | .app _ _ => intro h; exact nomatch h
  | .lam _ _ _ => intro h; exact nomatch h
  | .forallE _ _ _ => intro h; exact nomatch h
  | .letE _ _ _ => intro h; exact nomatch h
  | .lit _ => intro h; exact nomatch h
  | .proj _ _ _ => intro h; exact nomatch h
  | .const Dc usc => ?_
  intro h
  rw [if_pos rfl] at h
  try dsimp only at h
  revert h
  match hcinst : Expr.instPisAt
      (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f)) ++ fvs.drop rP)
      ((cvj.type.instantiateLevelParams cvj.levelParams
        lvls).renameConsts f) with
  | none => intro h; exact nomatch h
  | some (cdoms, cres) => ?_
  intro h
  try simp only [Except.bind, pure, Except.pure] at h
  try dsimp only at h
  by_cases hclen : cres.getAppArgs.length = cnP + (mI - rP)
  case neg => rw [if_neg hclen] at h; exact nomatch h
  rw [if_pos hclen] at h
  try dsimp only at h
  cases hdq1 : checkDefEqList (fueledOps mode F) env₀ (rP + cnF)
      ((lhsS.getAppArgs.drop rP).take (mI - rP))
      (cres.getAppArgs.drop cnP) with
  | error e => rw [hdq1] at h; exact nomatch h
  | ok u1 =>
  rw [hdq1] at h
  try dsimp only at h
  cases hdq2 : checkDefEqList (fueledOps mode F) env₀ (rP + cnF)
      ((fvs.drop rP).map Expr.fvarTypeD)
      (cdoms.drop cnP) with
  | error e => rw [hdq2] at h; exact nomatch h
  | ok u2 =>
  rw [hdq2] at h
  try dsimp only at h
  revert h
  match hrinst : Expr.instPisAt (fvs.take rP)
      (cvA.type.renameConsts f) with
  | none => intro h; exact nomatch h
  | some (rdoms, rrest) => ?_
  intro h
  try simp only [Except.bind, pure, Except.pure] at h
  try dsimp only at h
  cases hdq3 : checkDefEqList (fueledOps mode F) env₀ (rP + cnF)
      ((fvs.take rP).map Expr.fvarTypeD) rdoms with
  | error e => rw [hdq3] at h; exact nomatch h
  | ok u3 =>
  rw [hdq3] at h
  try dsimp only at h
  revert h
  match hopenP : openPisAtFvars rP cvA.type 0 with
  | none => intro h; exact nomatch h
  | some (fvsP, restP) => ?_
  intro h
  try simp only [Except.bind, pure, Except.pure] at h
  try dsimp only at h
  cases hannP : checkAnnotList (fueledOps mode F) env₀ (rP + cnF)
      (pins.map (fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p)) with
  | error e => rw [hannP] at h; exact nomatch h
  | ok uA =>
  rw [hannP] at h
  try dsimp only at h
  revert h
  match hcinstP : Expr.instPisAt
      (pins.map (fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p))
      (cvj.type.instantiateLevelParams cvj.levelParams lvls) with
  | none => intro h; exact nomatch h
  | some (cdomsP, crestP) => ?_
  intro h
  try simp only [Except.bind, pure, Except.pure] at h
  try dsimp only at h
  cases hdtP : checkTypedList (fueledOps mode F) env₀ (rP + cnF)
      (pins.map (fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p))
      cdomsP with
  | error e => rw [hdtP] at h; exact nomatch h
  | ok uP =>
  rw [hdtP] at h
  try dsimp only at h
  revert h
  match hopenX : openPisAtFvars cnF crestP rP with
  | none => intro h; exact nomatch h
  | some (xFvsP, crest2) => ?_
  intro h
  try simp only [Except.bind, pure, Except.pure] at h
  try dsimp only at h
  by_cases harX : (crest2.getAppArgs.length == cnP + (mI - rP)) = true
  case neg => rw [if_neg harX] at h; exact nomatch h
  rw [if_pos harX] at h
  try dsimp only at h
  revert h
  match hlinst : Expr.instLamsAt (fvsP ++ xFvsP) rhsA with
  | none => intro h; exact nomatch h
  | some (ldoms, lrest) => ?_
  intro h
  try simp only [Except.bind, pure, Except.pure] at h
  try dsimp only at h
  cases hdq4 : checkDefEqList (fueledOps mode F) env₀ (rP + cnF)
      ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldoms with
  | error e => rw [hdq4] at h; exact nomatch h
  | ok u4 =>
  rw [hdq4] at h
  try dsimp only at h
  revert h
  cases hde : isDefEqCore mode env₀ F (rP + cnF) rhsS
      (Expr.mkAppN (rhsA.renameConsts f) fvs) with
  | error e => intro h; exact nomatch h
  | ok v =>
  cases v with
  | false => intro h; simp at h
  | true =>
  intro h
  try simp only [Except.bind, pure, Except.pure] at h
  try dsimp only at h
  revert h
  cases htl : inferTypeCore mode env₀ F (rP + cnF) lhsS with
  | error e => intro h; exact nomatch h
  | ok tl => ?_
  intro h
  try dsimp only at h
  revert h
  cases hdl : isDefEqCore mode env₀ F (rP + cnF) tl αS with
  | error e => intro h; exact nomatch h
  | ok vl =>
  cases vl with
  | false => intro h; simp at h
  | true =>
  intro h
  try simp only [Except.bind, pure, Except.pure] at h
  try dsimp only at h
  revert h
  cases htr : inferTypeCore mode env₀ F (rP + cnF) rhsS with
  | error e => intro h; exact nomatch h
  | ok tr => ?_
  intro h
  try dsimp only at h
  revert h
  cases hdr : isDefEqCore mode env₀ F (rP + cnF) tr αS with
  | error e => intro h; exact nomatch h
  | ok vr =>
  cases vr with
  | false => intro h; simp at h
  | true =>
  intro h
  try simp only [Except.bind, pure, Except.pure] at h
  try dsimp only at h
  -- task #147: the slot-sort certification (task #146) is gated on the
  -- mode; split on the gate first
  cases htt : mode.ttChecks with
  | false =>
    rw [htt] at h
    simp only [Bool.false_eq_true, if_false, if_true, ite_true, pure,
      Except.pure, Bind.bind, Except.bind, Except.ok.injEq] at h
    exact Or.inr ⟨lvls, pins, h.symm, rfl,
          (cvA.name.str "_model").str s!"iota_{j}", cvt, ci, fvs,
          tbody, ℓA, αS, lhsS, rhsS, cdoms, cres, rdoms, rrest, fvsP,
          restP, cdomsP, crestP, xFvsP, crest2, ldoms, lrest,
          hfthm, hcvt, rfl, hlpt, hopen, hheadEq, hargs3, eq_of_beq hlhead, hlarity,
          eq_of_beq hlpre, Expr.ErasedEq.of_eq (eq_of_beq hmaj),
          ⟨bsC0, cbody0, Dc, usc, hcstrip, hcheadEq⟩,
          hcinst, hclen,
          checkDefEqList_inv hdq1, checkDefEqList_inv hdq2, hrinst,
          checkDefEqList_inv hdq3, hopenP, checkAnnotList_inv hannP,
          hcinstP,
          checkTypedList_inv hdtP, hopenX, eq_of_beq harX, hlinst,
          checkDefEqList_inv hdq4, hde, ⟨tl, htl, hdl⟩, ⟨tr, htr, hdr⟩,
          fun hc => absurd hc (by simp [htt])⟩
  | true =>
  rw [htt] at h
  simp only [if_true] at h
  revert h
  cases htα : inferTypeCore mode env₀ F (rP + cnF) αS with
  | error e => intro h; exact nomatch h
  | ok tα => ?_
  intro h
  try dsimp only at h
  revert h
  cases hdα : isDefEqCore mode env₀ F (rP + cnF) tα
      (Expr.sort (eqHeadLevel tbody.getAppFn)) with
  | error e => intro h; exact nomatch h
  | ok vα =>
  cases vα with
  | false => intro h; simp at h
  | true =>
  rw [hheadEq] at hdα
  intro h
  simp only [if_true, Except.ok.injEq] at h
  exact Or.inr ⟨lvls, pins, h.symm, rfl,
        (cvA.name.str "_model").str s!"iota_{j}", cvt, ci, fvs,
        tbody, ℓA, αS, lhsS, rhsS, cdoms, cres, rdoms, rrest, fvsP,
        restP, cdomsP, crestP, xFvsP, crest2, ldoms, lrest,
        hfthm, hcvt, rfl, hlpt, hopen, hheadEq, hargs3, eq_of_beq hlhead, hlarity,
        eq_of_beq hlpre, Expr.ErasedEq.of_eq (eq_of_beq hmaj),
        ⟨bsC0, cbody0, Dc, usc, hcstrip, hcheadEq⟩,
        hcinst, hclen,
        checkDefEqList_inv hdq1, checkDefEqList_inv hdq2, hrinst,
        checkDefEqList_inv hdq3, hopenP, checkAnnotList_inv hannP,
        hcinstP,
        checkTypedList_inv hdtP, hopenX, eq_of_beq harX, hlinst,
        checkDefEqList_inv hdq4, hde, ⟨tl, htl, hdl⟩, ⟨tr, htr, hdr⟩,
        fun _ => ⟨tα, htα, hdα⟩⟩

/-- The kernel-checked data of one modeled recursor rule: the
hypothesis kit its fold obligation consumes.  `env` is the environment
before the recursor group's installation, `env₀` the provisional one
with the block's rule-less recursors (in which the rule's right-hand
side was annotated). -/
@[expose] def RuleChecked (mode : CheckMode) (F : Nat) (env env₀ : Env) (f : Name → Name)
    (cvA : ConstantVal) (mI rP j : Nat) (r : RecRule) : Prop :=
  ∃ (cvj : ConstantVal) (cnP cnF : Nat) (raw rhsTy : Expr)
    (rbinders : List (Expr × BinderMeta)) (rbody : Expr),
    env.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF) ∧
    RecRule.nfields r = cnF ∧
    RecRule.ctorParams r = cnP ∧
    (RecRule.fire r = .plain ↔
      Expr.recRulePlain cvA.type mI rP cnP = true) ∧
    (∀ lvls pins, RecRule.fire r = .nested lvls pins →
      rP ≤ mI ∧
      (∀ l ∈ lvls, l.allParamsDefined cvA.levelParams = true) ∧
      (∀ pin ∈ pins, pin.hasFvar = false ∧
        pin.allLevelParamsDefined cvA.levelParams = true ∧
        pin.constsResolve env₀ = true ∧
        pin.looseBVarsBounded rP = true) ∧
      (∃ pre dom body bm D,
        cvA.type.stripPis mI = some (pre, .forallE dom body bm) ∧
        dom.getAppFn = .const D lvls ∧
        dom.getAppArgs =
          pins.map (Expr.liftLooseBVars (mI - rP) 0) ++
            (List.range (mI - rP)).map
              (fun i => Expr.bvar (mI - rP - 1 - i))) ∧
      pins.length = cnP ∧
      NestedChecked mode F env env₀ f cvA mI rP cnP cnF j r cvj lvls
        pins) ∧
    raw.hasFvar = false ∧ raw.looseBVarsBounded 0 = true ∧
    annotateCore mode env₀ F 0 raw = .ok (RecRule.rhs r) ∧
    (RecRule.rhs r).hasFvar = false ∧
    (RecRule.rhs r).looseBVarsBounded 0 = true ∧
    (RecRule.rhs r).allLevelParamsDefined cvA.levelParams = true ∧
    (RecRule.rhs r).constsResolve env₀ = true ∧
    (RecRule.rhs r).stripLams (rP + cnF) =
      some (rbinders, rbody) ∧
    inferTypeCore mode env₀ F 0 (RecRule.rhs r) = .ok rhsTy ∧
    (Expr.recRulePlain cvA.type mI rP cnP = true →
      PlainChecked mode F env env₀ f cvA mI rP cnP cnF j r cvj)

/-- Invert one `checkIotaRule` run. -/
theorem checkIotaRule_inv {env' env₀ : Env} {f : Name → Name}
    {cvA : ConstantVal} {mI rP j : Nat} {r r' : RecRule}
    (h : checkIotaRule mode (fueledOps mode F) env' env₀ f cvA.name cvA.levelParams
      cvA.type mI rP j r = .ok r') :
    RuleChecked mode F env' env₀ f cvA mI rP j r' ∧
      -- task #148 T6: the input-to-output link, which `RuleChecked`
      -- (stated over the *returned* rule alone) cannot carry: the
      -- returned rule is the input with its install-computed fields
      -- replaced, and
      -- the input's own right-hand side is the well-formed pre-image
      -- of the annotated one.  The proof always knew this; the
      -- statement now says so.
      (RecRule.rhs r).hasFvar = false ∧
      (RecRule.rhs r).looseBVarsBounded 0 = true ∧
      (∃ cnP fire rhsA,
        annotateCore mode env₀ F 0 (RecRule.rhs r) = .ok rhsA ∧
        r' = recRuleBits env'.find? cvA.name
          {r with rhs := rhsA, ctorParams := cnP, fire := fire,
                  paramsBlind := false} ∧
        (fire = .inert →
          nestedRuleShape env' env₀ cvA.name cvA.levelParams
            cvA.type mI rP cnP j = none) ∧
        (∀ lvls pins, fire = .nested lvls pins →
          nestedRuleShape env' env₀ cvA.name cvA.levelParams
            cvA.type mI rP cnP j = some (lvls, pins))) := by
  simp only [checkIotaRule, fueledOps_annotate, fueledOps_inferType,
    fueledOps_isDefEq, fueledOps_ensureSort, fueledOps_whnf, Bind.bind,
    Except.bind, pure, Except.pure] at h
  revert h
  match hfc : env'.find? (RecRule.ctor r) with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.ctorInfo cvj cnP cnF) => ?_
  intro h
  dsimp only at h
  by_cases hnf : RecRule.nfields r = cnF
  case neg => rw [if_neg hnf] at h; exact nomatch h
  rw [if_pos hnf] at h
  try dsimp only at h
  by_cases hrb : (RecRule.rhs r).looseBVarsBounded 0 = true
  case neg => rw [if_neg hrb] at h; exact nomatch h
  rw [if_pos hrb] at h
  try dsimp only at h
  by_cases hrf : (RecRule.rhs r).hasFvar = true
  case pos => rw [if_pos hrf] at h; exact nomatch h
  rw [if_neg hrf] at h
  have hrfF : (RecRule.rhs r).hasFvar = false := by
    revert hrf; cases (RecRule.rhs r).hasFvar <;> simp
  try dsimp only at h
  cases hann : annotateCore mode env₀ F 0 (RecRule.rhs r) with
  | error e => rw [hann] at h; exact nomatch h
  | ok rhsA =>
  rw [hann] at h
  try dsimp only at h
  by_cases hrlp : rhsA.allLevelParamsDefined cvA.levelParams = true
  case neg => rw [if_neg hrlp] at h; exact nomatch h
  rw [if_pos hrlp] at h
  try dsimp only at h
  by_cases hrres : rhsA.constsResolve env₀ = true
  case neg => rw [if_neg hrres] at h; exact nomatch h
  rw [if_pos hrres] at h
  try dsimp only at h
  by_cases hstrip : (rhsA.stripLams (rP + cnF)).isSome = true
  case neg => rw [if_neg hstrip] at h; exact nomatch h
  rw [if_pos hstrip] at h
  obtain ⟨⟨rbinders, rbody⟩, hstripEq⟩ :=
    Option.isSome_iff_exists.mp hstrip
  try dsimp only at h
  cases hity : inferTypeCore mode env₀ F 0 rhsA with
  | error e => rw [hity] at h; exact nomatch h
  | ok rhsTy =>
  rw [hity] at h
  try dsimp only at h
  by_cases hplain : Expr.recRulePlain cvA.type mI rP cnP = true
  case pos =>
    rw [if_pos hplain] at h
    revert h
    cases hthm : checkIotaThm mode (fueledOps mode F) env' env₀ f cvA.name
        cvA.levelParams cvA.type mI rP j r cvj cnP cnF rhsA with
    | error e => intro h; exact nomatch h
    | ok u =>
      intro h
      try dsimp only at h
      simp only [Except.ok.injEq] at h
      subst h
      have hkit := checkIotaThm_inv (cvA := cvA) hthm
      exact ⟨⟨cvj, cnP, cnF, RecRule.rhs r, rhsTy, rbinders, rbody,
        hfc, hnf, rfl, ⟨fun _ => hplain, fun _ => rfl⟩,
        fun lvls pins hf => RecRuleFire.noConfusion hf,
        hrfF, hrb, hann,
        not_hasFvar_of_fvarsBelow_zero
          ((annotateCore_WScoped F _ hann
            (WScoped.of_not_hasFvar hrfF)).fvarsBelow),
        annotateCore_looseBVars F _ hann hrb, hrlp, hrres, hstripEq,
        hity, fun _ => hkit⟩, hrfF, hrb,
        ⟨cnP, RecRuleFire.plain, rhsA, rfl, rfl,
          ⟨(fun hc => nomatch hc), (fun _ _ hc => nomatch hc)⟩⟩⟩
  case neg =>
    rw [if_neg hplain] at h
    revert h
    cases hthmN : checkIotaThmN mode (fueledOps mode F) env' env₀ f cvA.name
        cvA.levelParams cvA.type mI rP j r cvj cnP cnF rhsA with
    | error e => intro h; exact nomatch h
    | ok fire =>
      intro h
      try dsimp only at h
      simp only [Except.ok.injEq] at h
      subst h
      rcases checkIotaThmN_inv (cvA := cvA) hthmN with ⟨hinert, hnone⟩ |
        ⟨lvls, pins, hfe, hshape, hkit⟩
      · subst hinert
        exact ⟨⟨cvj, cnP, cnF, RecRule.rhs r, rhsTy, rbinders, rbody,
          hfc, hnf, rfl,
          ⟨fun hf => RecRuleFire.noConfusion hf,
            fun hc => absurd hc hplain⟩,
          fun lvls pins hf => RecRuleFire.noConfusion hf,
          hrfF, hrb, hann,
          not_hasFvar_of_fvarsBelow_zero
            ((annotateCore_WScoped F _ hann
              (WScoped.of_not_hasFvar hrfF)).fvarsBelow),
          annotateCore_looseBVars F _ hann hrb, hrlp, hrres, hstripEq,
          hity, fun hc => absurd hc hplain⟩, hrfF, hrb,
          ⟨cnP, RecRuleFire.inert, rhsA, rfl, rfl,
          ⟨(fun _ => hnone), (fun _ _ hc => nomatch hc)⟩⟩⟩
      · subst hfe
        refine ⟨⟨cvj, cnP, cnF, RecRule.rhs r, rhsTy, rbinders, rbody,
          hfc, hnf, rfl,
          ⟨fun hf => RecRuleFire.noConfusion hf,
            fun hc => absurd hc hplain⟩,
          ?_, hrfF, hrb, hann,
          not_hasFvar_of_fvarsBelow_zero
            ((annotateCore_WScoped F _ hann
              (WScoped.of_not_hasFvar hrfF)).fvarsBelow),
          annotateCore_looseBVars F _ hann hrb, hrlp, hrres, hstripEq,
          hity, fun hc => absurd hc hplain⟩, hrfF, hrb,
          ⟨cnP, RecRuleFire.nested lvls pins, rhsA, rfl, rfl,
          ⟨(fun hc => nomatch hc), (fun lvls' pins' hc => by
            obtain ⟨rfl, rfl⟩ := RecRuleFire.nested.inj hc
            exact hshape)⟩⟩⟩
        intro lvls' pins' hf
        obtain ⟨rfl, rfl⟩ := RecRuleFire.nested.inj
          (hf : RecRuleFire.nested lvls pins = .nested lvls' pins')
        obtain ⟨hmi, hlvls, hpins, pre, dom, body, bm, D, hstrip,
          hfn, hpinsEq, hpinsLen⟩ := nestedRuleShape_inv hshape
        exact ⟨hmi, hlvls, hpins,
          ⟨pre, dom, body, bm, D, hstrip, hfn, hpinsEq⟩, hpinsLen,
          hkit⟩

/-- Invert a successful `checkIotaRules` run: every returned rule
carries the full `RuleChecked` hypothesis kit. -/
theorem checkIotaRules_inv {env' env₀ : Env} {f : Name → Name}
    {cvA : ConstantVal} {mI rP : Nat} :
    ∀ (j : Nat) (rules rules' : List RecRule),
    checkIotaRules mode (fueledOps mode F) env' env₀ f cvA.name cvA.levelParams
      cvA.type mI rP j rules = .ok rules' →
    ∀ (k : Nat) (r' : RecRule), rules'[k]? = some r' →
      RuleChecked mode F env' env₀ f cvA mI rP (j + k) r' := by
  intro j rules
  induction rules generalizing j with
  | nil =>
    intro rules' h k r' hr'
    simp only [checkIotaRules, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp at hr'
  | cons r rest ih =>
    intro rules' h k r' hr'
    simp only [checkIotaRules, Bind.bind, Except.bind] at h
    revert h
    cases hr1 : checkIotaRule mode (fueledOps mode F) env' env₀ f cvA.name
        cvA.levelParams cvA.type mI rP j r with
    | error e => intro h; exact nomatch h
    | ok r₁ => ?_
    intro h
    try dsimp only at h
    revert h
    cases hrest : checkIotaRules mode (fueledOps mode F) env' env₀ f cvA.name
        cvA.levelParams cvA.type mI rP (j + 1) rest with
    | error e => intro h; exact nomatch h
    | ok rest' => ?_
    intro h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hr'
      subst hr'
      simpa using (checkIotaRule_inv hr1).1
    | succ k' =>
      simp only [List.getElem?_cons_succ] at hr'
      have hik := ih (j + 1) rest' hrest k' r' hr'
      simpa [Nat.add_assoc, Nat.add_comm 1 k'] using hik

set_option maxHeartbeats 1600000 in
/-- The kernel-checked eta pins of a block's capability record,
carried through the member fold: `find?`-facts (preserved by fresh
installs) and plain syntax about the model-side statement.  The last
conjunct of each half is task #135's: the model former's telescope
residual is `Sort ℓA` at the statement's own `Eq` level, which is what
lets a consumer type the equation's type slot at the level the
statement names (see `checkEtaThm`). -/
@[expose] def EtaPins (mode : CheckMode) (env' : Env) (T : Name) (lps : List Name)
    (caps : IndCaps) : Prop :=
  (caps.eta = true →
  ∃ (tcv : ConstantVal) (tval : Expr) (cvmT : ConstantVal) (mvalT : Expr)
    (hmcvmT : ReducibilityHint)
    (sbinders tbindersM : List (Expr × BinderMeta))
    (sbody tbodyM tySlot : Expr) (ℓA : Level),
    env'.find? ((T.str "_model").str "eta") = some (.thmInfo tcv tval) ∧
    tcv.levelParams = lps ∧
    env'.find? (T.str "_model") = some (.defnInfo cvmT mvalT hmcvmT) ∧
    cvmT.levelParams = lps ∧
    (∃ cvmC mvalC hmcvmC, env'.find? (caps.etaCtor.str "_model") =
      some (.defnInfo cvmC mvalC hmcvmC) ∧ cvmC.levelParams = lps) ∧
    (∀ j, j < caps.etaFields → ∃ cvmj mvalj hmcvmj,
      env'.find? (projModelName T j) = some (.defnInfo cvmj mvalj hmcvmj) ∧
      cvmj.levelParams = lps) ∧
    env'.find? eqName = some eqA ∧
    tcv.type.stripPis (caps.etaParams + 1) = some (sbinders, sbody) ∧
    cvmT.type.stripPis caps.etaParams = some (tbindersM, tbodyM) ∧
    (∀ (k : Nat) (b b' : Expr × BinderMeta), k < caps.etaParams →
      sbinders[k]? = some b → tbindersM[k]? = some b' →
      b.1 = b'.1) ∧
    (∃ mx, sbinders[caps.etaParams]? = some (
      Expr.mkAppN (.const (T.str "_model") (lps.map .param))
        ((List.range caps.etaParams).map fun k =>
          Expr.bvar (caps.etaParams - 1 - k)), mx)) ∧
    sbody = Expr.mkAppN (.const eqName [ℓA])
      [tySlot, .bvar 0,
       Expr.mkAppN (.const (caps.etaCtor.str "_model") (lps.map .param))
        (((List.range caps.etaParams).map fun k =>
            Expr.bvar (caps.etaParams - k)) ++
         (List.range caps.etaFields).map fun j => Expr.mkAppN
           (.const (projModelName T j) (lps.map .param))
           (((List.range caps.etaParams).map fun k =>
               Expr.bvar (caps.etaParams - k)) ++
            [Expr.bvar 0]))] ∧
    tySlot = Expr.mkAppN (.const (T.str "_model") (lps.map .param))
      ((List.range caps.etaParams).map fun k =>
        Expr.bvar (caps.etaParams - k)) ∧
    -- TT-lane conjunct (task #147): delivered only at `mode.ttChecks`
    (mode.ttChecks = true → tbodyM = Expr.sort ℓA)) ∧
  (caps.unitlike = true →
  ∃ (tcv : ConstantVal) (tval : Expr) (cvmT : ConstantVal) (mvalT : Expr)
    (hmcvmT : ReducibilityHint)
    (sbinders tbindersM : List (Expr × BinderMeta))
    (sbody tbodyM tySlot : Expr) (ℓA : Level),
    env'.find? ((T.str "_model").str "unitlike") =
      some (.thmInfo tcv tval) ∧
    tcv.levelParams = lps ∧
    env'.find? (T.str "_model") = some (.defnInfo cvmT mvalT hmcvmT) ∧
    cvmT.levelParams = lps ∧
    env'.find? eqName = some eqA ∧
    tcv.type.stripPis (caps.unitParams + 2) = some (sbinders, sbody) ∧
    cvmT.type.stripPis caps.unitParams = some (tbindersM, tbodyM) ∧
    (∀ (k : Nat) (b b' : Expr × BinderMeta),
      k < caps.unitParams →
      sbinders[k]? = some b → tbindersM[k]? = some b' →
      b.1 = b'.1) ∧
    (∃ mx, sbinders[caps.unitParams]? = some (
      Expr.mkAppN (.const (T.str "_model") (lps.map .param))
        ((List.range caps.unitParams).map fun k =>
          Expr.bvar (caps.unitParams - 1 - k)), mx)) ∧
    (∃ my, sbinders[caps.unitParams + 1]? = some (
      Expr.mkAppN (.const (T.str "_model") (lps.map .param))
        ((List.range caps.unitParams).map fun k =>
          Expr.bvar (caps.unitParams - k)), my)) ∧
    sbody = Expr.mkAppN (.const eqName [ℓA]) [tySlot, .bvar 1, .bvar 0] ∧
    tySlot = Expr.mkAppN (.const (T.str "_model") (lps.map .param))
      ((List.range caps.unitParams).map fun k =>
        Expr.bvar (caps.unitParams + 1 - k)) ∧
    -- TT-lane conjunct (task #147): delivered only at `mode.ttChecks`
    (mode.ttChecks = true → tbodyM = Expr.sort ℓA))

set_option maxHeartbeats 3200000 in
/-- Invert a positive unit-capability check into the stored pins. -/
theorem checkUnitThm_inv {env' : Env} {T : Name}
    {lps : List Name} {nP : Nat}
    (h : checkUnitThm mode env' T lps nP = true) :
    ∃ (tcv : ConstantVal) (tval : Expr) (cvmT : ConstantVal)
      (mvalT : Expr) (hmcvmT : ReducibilityHint)
      (sbinders tbindersM : List (Expr × BinderMeta))
      (sbody tbodyM tySlot : Expr) (ℓA : Level),
      env'.find? ((T.str "_model").str "unitlike") =
        some (.thmInfo tcv tval) ∧
      tcv.levelParams = lps ∧
      env'.find? (T.str "_model") = some (.defnInfo cvmT mvalT hmcvmT) ∧
      cvmT.levelParams = lps ∧
      env'.find? eqName = some eqA ∧
      tcv.type.stripPis (nP + 2) = some (sbinders, sbody) ∧
      cvmT.type.stripPis nP = some (tbindersM, tbodyM) ∧
      (∀ (k : Nat) (b b' : Expr × BinderMeta), k < nP →
        sbinders[k]? = some b → tbindersM[k]? = some b' →
        b.1 = b'.1) ∧
      (∃ mx, sbinders[nP]? = some (
        Expr.mkAppN (.const (T.str "_model") (lps.map .param))
          ((List.range nP).map fun k => Expr.bvar (nP - 1 - k)), mx)) ∧
      (∃ my, sbinders[nP + 1]? = some (
        Expr.mkAppN (.const (T.str "_model") (lps.map .param))
          ((List.range nP).map fun k => Expr.bvar (nP - k)), my)) ∧
      sbody = Expr.mkAppN (.const eqName [ℓA])
        [tySlot, .bvar 1, .bvar 0] ∧
      tySlot = Expr.mkAppN (.const (T.str "_model") (lps.map .param))
        ((List.range nP).map fun k => Expr.bvar (nP + 1 - k)) ∧
      (mode.ttChecks = true → tbodyM = Expr.sort ℓA) := by
  rw [checkUnitThm] at h
  revert h
  match hthm : env'.find? ((T.str "_model").str "unitlike") with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.thmInfo tcv tval) => ?_
  intro h
  revert h
  match hTm : env'.find? (T.str "_model") with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.defnInfo cvmT mvalT hmcvmT) => ?_
  intro h
  revert h
  match heqf : env'.find? eqName with
  | none => intro h; exact nomatch h
  | some eqStored => ?_
  intro h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨heqA, htlps⟩, hTlps⟩ := h.1
  have hrest := h.2
  revert hrest
  match hS_strip : tcv.type.stripPis (nP + 2) with
  | none => intro hrest; exact nomatch hrest
  | some (sbinders, sbody) => ?_
  intro hrest
  revert hrest
  match hTm_strip : cvmT.type.stripPis nP with
  | none => intro hrest; exact nomatch hrest
  | some (tbindersM, tbodyM) => ?_
  intro hrest
  simp only [Bool.and_eq_true] at hrest
  obtain ⟨⟨⟨hdomsB, hxdomB⟩, hydomB⟩, hbodyB⟩ := hrest
  have hdoms : ∀ (k : Nat) (b b' : Expr × BinderMeta), k < nP →
      sbinders[k]? = some b → tbindersM[k]? = some b' →
      b.1 = b'.1 := by
    intro k b b' hk hb hb'
    exact domsMatchAux_inv hdomsB hk
      (by rw [Nat.zero_add]; exact hb) (by rw [Nat.zero_add]; exact hb')
  have hxdom : ∃ mx, sbinders[nP]? = some (
      Expr.mkAppN (.const (T.str "_model") (lps.map .param))
        ((List.range nP).map fun k => Expr.bvar (nP - 1 - k)), mx) := by
    revert hxdomB
    match hbx : sbinders[nP]? with
    | none => intro hx; exact nomatch hx
    | some (xdom, mx) =>
      intro hx
      exact ⟨mx, by rw [eq_of_beq hx]⟩
  have hydom : ∃ my, sbinders[nP + 1]? = some (
      Expr.mkAppN (.const (T.str "_model") (lps.map .param))
        ((List.range nP).map fun k => Expr.bvar (nP - k)), my) := by
    revert hydomB
    match hby : sbinders[nP + 1]? with
    | none => intro hy; exact nomatch hy
    | some (ydom, my) =>
      intro hy
      exact ⟨my, by rw [eq_of_beq hy]⟩
  revert hbodyB
  match hsb : sbody with
  | .app (.app (.app (.const c ℓs) tySlot) lhsC) rhsC => ?_
  | .bvar _ => intro hb; exact nomatch hb
  | .fvar _ _ => intro hb; exact nomatch hb
  | .sort _ => intro hb; exact nomatch hb
  | .const _ _ => intro hb; exact nomatch hb
  | .lam _ _ _ => intro hb; exact nomatch hb
  | .forallE _ _ _ => intro hb; exact nomatch hb
  | .letE _ _ _ => intro hb; exact nomatch hb
  | .lit _ => intro hb; exact nomatch hb
  | .proj _ _ _ => intro hb; exact nomatch hb
  | .app (.bvar _) _ => intro hb; exact nomatch hb
  | .app (.fvar _ _) _ => intro hb; exact nomatch hb
  | .app (.sort _) _ => intro hb; exact nomatch hb
  | .app (.const _ _) _ => intro hb; exact nomatch hb
  | .app (.lam _ _ _) _ => intro hb; exact nomatch hb
  | .app (.forallE _ _ _) _ => intro hb; exact nomatch hb
  | .app (.letE _ _ _) _ => intro hb; exact nomatch hb
  | .app (.lit _) _ => intro hb; exact nomatch hb
  | .app (.proj _ _ _) _ => intro hb; exact nomatch hb
  | .app (.app (.bvar _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.fvar _ _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.sort _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.const _ _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.lam _ _ _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.forallE _ _ _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.letE _ _ _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.lit _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.proj _ _ _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.app (.bvar _) _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.app (.fvar _ _) _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.app (.sort _) _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.app (.app _ _) _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.app (.lam _ _ _) _) _) _ =>
    intro hb; exact nomatch hb
  | .app (.app (.app (.forallE _ _ _) _) _) _ =>
    intro hb; exact nomatch hb
  | .app (.app (.app (.letE _ _ _) _) _) _ =>
    intro hb; exact nomatch hb
  | .app (.app (.app (.lit _) _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.app (.proj _ _ _) _) _) _ =>
    intro hb; exact nomatch hb
  intro hb
  revert hb
  match ℓs with
  | [] => intro hb; exact nomatch hb
  | _ :: _ :: _ => intro hb; exact nomatch hb
  | [ℓA] => ?_
  intro hb
  simp only [Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨hceq, hlhs⟩, hrhs⟩, hts⟩, hsortM⟩ := hb
  refine ⟨tcv, tval, cvmT, mvalT, hmcvmT, sbinders, tbindersM, _, tbodyM,
    tySlot, ℓA, rfl, eq_of_beq htlps, rfl, eq_of_beq hTlps,
    (by rw [eq_of_beq heqA]), hS_strip, hTm_strip, hdoms, hxdom, hydom,
    ?_, eq_of_beq hts,
    fun htt => eq_of_beq (by simpa [htt] using hsortM)⟩
  rw [eq_of_beq hceq, eq_of_beq hlhs, eq_of_beq hrhs]
  rfl

set_option maxHeartbeats 3200000 in
/-- Invert a positive eta-capability check into the stored pins. -/
theorem checkEtaThm_inv {env' : Env} {T ctorName : Name}
    {lps : List Name} {nP nF : Nat}
    (h : checkEtaThm mode env' T ctorName lps nP nF = true) :
    ∃ (tcv : ConstantVal) (tval : Expr) (cvmT : ConstantVal)
      (mvalT : Expr) (hmcvmT : ReducibilityHint)
      (sbinders tbindersM : List (Expr × BinderMeta))
      (sbody tbodyM tySlot : Expr) (ℓA : Level),
      env'.find? ((T.str "_model").str "eta") =
        some (.thmInfo tcv tval) ∧
      tcv.levelParams = lps ∧
      env'.find? (T.str "_model") = some (.defnInfo cvmT mvalT hmcvmT) ∧
      cvmT.levelParams = lps ∧
      (∃ cvmC mvalC hmcvmC, env'.find? (ctorName.str "_model") =
        some (.defnInfo cvmC mvalC hmcvmC) ∧ cvmC.levelParams = lps) ∧
      (∀ j, j < nF → ∃ cvmj mvalj hmcvmj,
        env'.find? (projModelName T j) = some (.defnInfo cvmj mvalj hmcvmj) ∧
        cvmj.levelParams = lps) ∧
      env'.find? eqName = some eqA ∧
      tcv.type.stripPis (nP + 1) = some (sbinders, sbody) ∧
      cvmT.type.stripPis nP = some (tbindersM, tbodyM) ∧
      (∀ (k : Nat) (b b' : Expr × BinderMeta), k < nP →
        sbinders[k]? = some b → tbindersM[k]? = some b' →
        b.1 = b'.1) ∧
      (∃ mx, sbinders[nP]? = some (
        Expr.mkAppN (.const (T.str "_model") (lps.map .param))
          ((List.range nP).map fun k => Expr.bvar (nP - 1 - k)), mx)) ∧
      sbody = Expr.mkAppN (.const eqName [ℓA])
        [tySlot, .bvar 0,
         Expr.mkAppN (.const (ctorName.str "_model") (lps.map .param))
          (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
           (List.range nF).map fun j => Expr.mkAppN
             (.const (projModelName T j) (lps.map .param))
             (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
              [Expr.bvar 0]))] ∧
      tySlot = Expr.mkAppN (.const (T.str "_model") (lps.map .param))
        ((List.range nP).map fun k => Expr.bvar (nP - k)) ∧
      (mode.ttChecks = true → tbodyM = Expr.sort ℓA) := by
  rw [checkEtaThm] at h
  revert h
  match hthm : env'.find? ((T.str "_model").str "eta") with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.thmInfo tcv tval) => ?_
  intro h
  revert h
  match hTm : env'.find? (T.str "_model") with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.defnInfo cvmT mvalT hmcvmT) => ?_
  intro h
  revert h
  match hCm : env'.find? (ctorName.str "_model") with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.defnInfo cvmC mvalC hmcvmC) => ?_
  intro h
  revert h
  match heqf : env'.find? eqName with
  | none => intro h; exact nomatch h
  | some eqStored => ?_
  intro h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨heqA, htlps⟩, hTlps⟩, hClps⟩, hproj⟩, hrest⟩ := h
  have hprojf : ∀ j, j < nF → ∃ cvmj mvalj hmcvmj,
      env'.find? (projModelName T j) = some (.defnInfo cvmj mvalj hmcvmj) ∧
      cvmj.levelParams = lps := by
    intro j hj
    have h1 := List.all_eq_true.mp hproj j (List.mem_range.mpr hj)
    revert h1
    match hfj : env'.find? (projModelName T j) with
    | none => intro h1; exact nomatch h1
    | some (.axiomInfo _) => intro h1; exact nomatch h1
    | some (.projInfo _) => intro h1; exact nomatch h1
    | some (.thmInfo _ _) => intro h1; exact nomatch h1
    | some (.indInfo _ _) => intro h1; exact nomatch h1
    | some (.ctorInfo _ _ _) => intro h1; exact nomatch h1
    | some (.recInfo _ _ _ _) => intro h1; exact nomatch h1
    | some (.defnInfo cvmj mvalj hmcvmj) =>
      intro h1
      exact ⟨cvmj, mvalj, hmcvmj, rfl, eq_of_beq h1⟩
  revert hrest
  match hS_strip : tcv.type.stripPis (nP + 1) with
  | none => intro hrest; exact nomatch hrest
  | some (sbinders, sbody) => ?_
  intro hrest
  revert hrest
  match hTm_strip : cvmT.type.stripPis nP with
  | none => intro hrest; exact nomatch hrest
  | some (tbindersM, tbodyM) => ?_
  intro hrest
  simp only [Bool.and_eq_true] at hrest
  obtain ⟨⟨hdomsB, hxdomB⟩, hbodyB⟩ := hrest
  have htMlen : tbindersM.length = nP := Expr.stripPis_length _ hTm_strip
  have hdoms : ∀ (k : Nat) (b b' : Expr × BinderMeta), k < nP →
      sbinders[k]? = some b → tbindersM[k]? = some b' →
      b.1 = b'.1 := by
    intro k b b' hk hb hb'
    exact domsMatchAux_inv hdomsB hk
      (by rw [Nat.zero_add]; exact hb) (by rw [Nat.zero_add]; exact hb')
  have hxdom : ∃ mx, sbinders[nP]? = some (
      Expr.mkAppN (.const (T.str "_model") (lps.map .param))
        ((List.range nP).map fun k => Expr.bvar (nP - 1 - k)), mx) := by
    revert hxdomB
    match hbx : sbinders[nP]? with
    | none => intro hx; exact nomatch hx
    | some (xdom, mx) =>
      intro hx
      exact ⟨mx, by rw [eq_of_beq hx]⟩
  revert hbodyB
  match hsb : sbody with
  | .app (.app (.app (.const c ℓs) tySlot) lhsC) rhsC => ?_
  | .bvar _ => intro hb; exact nomatch hb
  | .fvar _ _ => intro hb; exact nomatch hb
  | .sort _ => intro hb; exact nomatch hb
  | .const _ _ => intro hb; exact nomatch hb
  | .lam _ _ _ => intro hb; exact nomatch hb
  | .forallE _ _ _ => intro hb; exact nomatch hb
  | .letE _ _ _ => intro hb; exact nomatch hb
  | .lit _ => intro hb; exact nomatch hb
  | .proj _ _ _ => intro hb; exact nomatch hb
  | .app (.bvar _) _ => intro hb; exact nomatch hb
  | .app (.fvar _ _) _ => intro hb; exact nomatch hb
  | .app (.sort _) _ => intro hb; exact nomatch hb
  | .app (.const _ _) _ => intro hb; exact nomatch hb
  | .app (.lam _ _ _) _ => intro hb; exact nomatch hb
  | .app (.forallE _ _ _) _ => intro hb; exact nomatch hb
  | .app (.letE _ _ _) _ => intro hb; exact nomatch hb
  | .app (.lit _) _ => intro hb; exact nomatch hb
  | .app (.proj _ _ _) _ => intro hb; exact nomatch hb
  | .app (.app (.bvar _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.fvar _ _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.sort _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.const _ _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.lam _ _ _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.forallE _ _ _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.letE _ _ _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.lit _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.proj _ _ _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.app (.bvar _) _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.app (.fvar _ _) _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.app (.sort _) _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.app (.app _ _) _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.app (.lam _ _ _) _) _) _ =>
    intro hb; exact nomatch hb
  | .app (.app (.app (.forallE _ _ _) _) _) _ =>
    intro hb; exact nomatch hb
  | .app (.app (.app (.letE _ _ _) _) _) _ =>
    intro hb; exact nomatch hb
  | .app (.app (.app (.lit _) _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.app (.proj _ _ _) _) _) _ =>
    intro hb; exact nomatch hb
  intro hb
  revert hb
  match ℓs with
  | [] => intro hb; exact nomatch hb
  | _ :: _ :: _ => intro hb; exact nomatch hb
  | [ℓA] => ?_
  intro hb
  simp only [Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨hceq, hlhs⟩, hts⟩, hrhs⟩, hsortM⟩ := hb
  refine ⟨tcv, tval, cvmT, mvalT, hmcvmT, sbinders, tbindersM, _, tbodyM,
    tySlot, ℓA, rfl, eq_of_beq htlps, rfl, eq_of_beq hTlps,
    ⟨cvmC, mvalC, hmcvmC, rfl, eq_of_beq hClps⟩, hprojf,
    (by rw [eq_of_beq heqA]), hS_strip,
    hTm_strip, hdoms, hxdom, ?_, eq_of_beq hts,
    fun htt => eq_of_beq (by simpa [htt] using hsortM)⟩
  rw [eq_of_beq hceq, eq_of_beq hlhs, eq_of_beq hrhs]
  rfl

/-- The pins persist under a fresh install. -/
theorem EtaPins.step {env' : Env} {c₁ : ConstantInfo} {T : Name}
    {lps : List Name} {caps : IndCaps}
    (h : EtaPins mode env' T lps caps)
    (hfresh : env'.find? c₁.name = none) :
    EtaPins mode ⟨c₁ :: env'.consts⟩ T lps caps := by
  have hkeep : ∀ (n : Name) (ci : ConstantInfo),
      env'.find? n = some ci →
      (⟨c₁ :: env'.consts⟩ : Env).find? n = some ci := by
    intro n ci hf
    rw [Env.find?_cons, if_neg ?_]
    · exact hf
    · intro he
      rw [← he, hfresh] at hf
      exact nomatch hf
  refine ⟨?_, ?_⟩
  · intro hcape
    obtain ⟨tcv, tval, cvmT, mvalT, hmT, sbinders, tbindersM, sbody, tbodyM,
      tySlot, ℓA, hthm, h2, hTm, h4, ⟨cvmC, mvalC, hmC, hCm, hClps⟩, hPj,
      heqf, h8, h9, h10, h11, h12, h13⟩ := h.1 hcape
    refine ⟨tcv, tval, cvmT, mvalT, hmT, sbinders, tbindersM, sbody, tbodyM,
      tySlot, ℓA, hkeep _ _ hthm, h2, hkeep _ _ hTm, h4,
      ⟨cvmC, mvalC, hmC, hkeep _ _ hCm, hClps⟩, ?_, hkeep _ _ heqf,
      h8, h9, h10, h11, h12, h13⟩
    intro j hj
    obtain ⟨cvmj, mvalj, hmj, hfj, hjlps⟩ := hPj j hj
    exact ⟨cvmj, mvalj, hmj, hkeep _ _ hfj, hjlps⟩
  · intro hcapu
    obtain ⟨tcv, tval, cvmT, mvalT, hmT, sbinders, tbindersM, sbody, tbodyM,
      tySlot, ℓA, hthm, h2, hTm, h4, heqf, h6, h7, h8, h9, h10, h11, h12⟩ :=
      h.2 hcapu
    exact ⟨tcv, tval, cvmT, mvalT, hmT, sbinders, tbindersM, sbody, tbodyM,
      tySlot, ℓA, hkeep _ _ hthm, h2, hkeep _ _ hTm, h4,
      hkeep _ _ heqf, h6, h7, h8, h9, h10, h11, h12⟩


/-- The pins transport along any lookup preservation covering the
non-recursor kinds (the pins only look up theorems, definitions and
the pinned equality former). -/
theorem EtaPins.transport {env₁ env₂ : Env} {T : Name}
    {lps : List Name} {caps : IndCaps}
    (h : EtaPins mode env₁ T lps caps)
    (hkeep : ∀ (n : Name) (ci : ConstantInfo), env₁.find? n = some ci →
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      env₂.find? n = some ci) :
    EtaPins mode env₂ T lps caps := by
  have hk : ∀ (n : Name) (cv : ConstantVal) (tv : Expr),
      env₁.find? n = some (.thmInfo cv tv) →
      env₂.find? n = some (.thmInfo cv tv) :=
    fun n cv tv hf => hkeep n _ hf (fun _ _ _ _ hc => nomatch hc)
  have hkd : ∀ (n : Name) (cv : ConstantVal) (v : Expr)
      (hh : ReducibilityHint), env₁.find? n = some (.defnInfo cv v hh) →
      env₂.find? n = some (.defnInfo cv v hh) :=
    fun n cv v hh hf => hkeep n _ hf (fun _ _ _ _ hc => nomatch hc)
  have hke : env₁.find? eqName = some eqA →
      env₂.find? eqName = some eqA :=
    fun hf => hkeep _ _ hf (fun _ _ _ _ hc => nomatch hc)
  refine ⟨?_, ?_⟩
  · intro hcape
    obtain ⟨tcv, tval, cvmT, mvalT, hmT, sbinders, tbindersM, sbody, tbodyM,
      tySlot, ℓA, hthm, h2, hTm, h4, ⟨cvmC, mvalC, hmC, hCm, hClps⟩, hPj,
      heqf, h8, h9, h10, h11, h12, h13⟩ := h.1 hcape
    refine ⟨tcv, tval, cvmT, mvalT, hmT, sbinders, tbindersM, sbody, tbodyM,
      tySlot, ℓA, hk _ _ _ hthm, h2, hkd _ _ _ _ hTm, h4,
      ⟨cvmC, mvalC, hmC, hkd _ _ _ _ hCm, hClps⟩, ?_, hke heqf,
      h8, h9, h10, h11, h12, h13⟩
    intro j hj
    obtain ⟨cvmj, mvalj, hmj, hfj, hjlps⟩ := hPj j hj
    exact ⟨cvmj, mvalj, hmj, hkd _ _ _ _ hfj, hjlps⟩
  · intro hcapu
    obtain ⟨tcv, tval, cvmT, mvalT, hmT, sbinders, tbindersM, sbody, tbodyM,
      tySlot, ℓA, hthm, h2, hTm, h4, heqf, h6, h7, h8, h9, h10, h11, h12⟩ :=
      h.2 hcapu
    exact ⟨tcv, tval, cvmT, mvalT, hmT, sbinders, tbindersM, sbody, tbodyM,
      tySlot, ℓA, hk _ _ _ hthm, h2, hkd _ _ _ _ hTm, h4,
      hke heqf, h6, h7, h8, h9, h10, h11, h12⟩


/-! ## The block fold's eta side invariant

`EtaPins` speaks about the members still *ahead* of a block fold; the
eta head obligation at a member install is about a family that may
already be stored, and about the run's projection freshness.  Both are
`V`-free, both step at every install, and both are supplied at the
assembly.  The eta head obligation is a threaded *invariant*, not an
obligation forwarded to the caller: its dead cases die on facts that
hold at every install — the member's own `isProjFnShape = false` guard,
the closedness of outside eta families, and `BlockEtaPinned`'s unstored
first projection — leaving only the 0-field family, whose law fires with
its projection premises vacuous. -/

/-- **Every stored eta-capable block former carries what its family's
completion needs**: its `EtaPins`, a capability constructor that is
itself a block member (so the block invariant's public/model
identification reaches it), and — when it has fields — the freshness
of its first projection, which is what makes a `etaFields > 0` family
unable to complete before the projection fold runs. -/
@[expose] def BlockEtaPinned (mode : CheckMode) (blockNames : List Name)
    (env : Env) : Prop :=
  ∀ (n : Name) (cvS : ConstantVal) (capsS : IndCaps),
    blockNames.contains n = true →
    env.find? n = some (.indInfo cvS capsS) → capsS.eta = true →
    EtaPins mode env n cvS.levelParams capsS ∧
      blockNames.contains capsS.etaCtor = true ∧
      (0 < capsS.etaFields → env.find? (projFnName n 0) = none)

/-- A projection function's name is never a block member's: block
members are guarded `isProjFnShape = false`. -/
theorem projFnName_ne_of_shape {T n : Name} {j : Nat}
    (h : n.isProjFnShape = false) : projFnName T j ≠ n := by
  intro he
  rw [← he] at h
  simp [projFnName, Name.isProjFnShape] at h

/-- The stored-pins invariant steps at any fresh install whose name is
not projection-shaped, given the new member's own data when it is an
eta-capable former. -/
theorem BlockEtaPinned.cons {mode : CheckMode} {blockNames : List Name}
    {env : Env} {c₀ : ConstantInfo}
    (h : BlockEtaPinned mode blockNames env)
    (hfresh : env.find? c₀.name = none)
    (hshape : c₀.name.isProjFnShape = false)
    (hnew : ∀ cvS capsS, c₀ = .indInfo cvS capsS → capsS.eta = true →
      EtaPins mode env c₀.name cvS.levelParams capsS ∧
        blockNames.contains capsS.etaCtor = true ∧
        (0 < capsS.etaFields →
          env.find? (projFnName c₀.name 0) = none)) :
    BlockEtaPinned mode blockNames ⟨c₀ :: env.consts⟩ := by
  have hup : ∀ n : Name, env.find? (projFnName n 0) = none →
      (⟨c₀ :: env.consts⟩ : Env).find? (projFnName n 0) = none := by
    intro n hn
    rw [Env.find?_cons, if_neg (fun he =>
      projFnName_ne_of_shape (T := n) (j := 0) hshape he.symm)]
    exact hn
  intro n cvS capsS hnb hf hcape
  rw [Env.find?_cons] at hf
  split at hf
  · next he =>
    obtain rfl : c₀ = .indInfo cvS capsS := Option.some.inj hf
    obtain ⟨hp, hc, hj⟩ := hnew cvS capsS rfl hcape
    exact ⟨he ▸ EtaPins.step hp hfresh, hc,
      fun hlt => he ▸ hup _ (hj hlt)⟩
  · obtain ⟨hp, hc, hj⟩ := h n cvS capsS hnb hf hcape
    exact ⟨EtaPins.step hp hfresh, hc, fun hlt => hup n (hj hlt)⟩

/-- **The block's capability pins**, from the capability record's own
definition: `indBlockCaps`' two Booleans *are* `checkEtaThm` and
`checkUnitThm`, which invert to the artifacts' shape pins.  Transpose
of `Model/Extend/Decl.lean`'s `hpinsT0`. -/
theorem etaPins_of_indBlockCaps {μ : CheckMode} {env : Env}
    {cvT cvC : ConstantVal} {nP nF : Nat} :
    EtaPins μ env cvT.name cvT.levelParams
      (indBlockCaps μ env cvT cvC nP nF) := by
  refine ⟨?_, ?_⟩
  · intro hcape
    simp only [indBlockCaps, Bool.and_eq_true] at hcape
    exact checkEtaThm_inv hcape.2
  · intro hcapu
    simp only [indBlockCaps] at hcapu
    exact checkUnitThm_inv hcapu

/-- **A stored inductive member's capability arities** (`IndCapsWF` on
the modeled route), from checks the install already makes: a
capability's pin reads the model former's `∀`-telescope at the
parameter count (`checkEtaThm`/`checkUnitThm`, through `EtaPins`),
and the member's stored type is the model's under the block renaming
(`checkMemberVal`), which keeps the telescope. -/
theorem indCapsWF_of_pins {μ : CheckMode} {env : Env} {cvA : ConstantVal}
    {caps : IndCaps} {f : Name → Name}
    (hpins : EtaPins μ env cvA.name cvA.levelParams caps)
    {cvm : ConstantVal} {mval : Expr} {hint : ReducibilityHint}
    (hfm : env.find? (cvA.name.str "_model") =
      some (.defnInfo cvm mval hint))
    (hty : (cvA.type.renameConsts f == cvm.type) = true) :
    IndCapsWF (.indInfo cvA caps) := by
  have hty' : cvA.type.renameConsts f = cvm.type := eq_of_beq hty
  refine IndCapsWF.of_caps ?_ ?_
  · intro hu
    obtain ⟨_, _, cvmT, _, _, _, _, _, _, _, _, -, -, hfmT, -, -, -,
      hstrip, -⟩ := hpins.2 hu
    rw [hfm] at hfmT
    obtain ⟨rfl, -, -⟩ := ConstantInfo.defnInfo.inj (Option.some.inj hfmT)
    exact Expr.stripPis_isSome_of_renameConsts (f := f) _
      (by rw [hty', hstrip]; rfl)
  · intro he
    obtain ⟨_, _, cvmT, _, _, _, _, _, _, _, _, -, -, hfmT, -, -, -, -, -,
      hstrip, -⟩ := hpins.1 he
    rw [hfm] at hfmT
    obtain ⟨rfl, -, -⟩ := ConstantInfo.defnInfo.inj (Option.some.inj hfmT)
    exact Expr.stripPis_isSome_of_renameConsts (f := f) _
      (by rw [hty', hstrip]; rfl)

end ConLeche
