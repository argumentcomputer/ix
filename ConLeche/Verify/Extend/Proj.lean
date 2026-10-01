module

public import ConLeche.Verify.Extend.Modeled

public section

/-!
# Proj

The `checkProjFn` stage inversions (lookups, type, rule, iota theorem,
shape, and the whole-function inversion) and the `checkProjFold`
bookkeeping family.

Every statement is over `Env`/`Expr` alone; the projection phase's
valuation-carrying invariant and soundness statements are one tier up
(`ConLeche/Semantics/ProjPhase.lean`,
`ConLeche/Semantics/Bridge/DeclIndRun.lean`).
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

variable {mode : CheckMode}

open Expr

/-- Invert stage 1 of `checkProjFn` (the stored-constant lookups). -/
theorem checkProjLookups_inv {env' : Env} {T ctorName : Name}
    {lps : List Name} {nP nF i : Nat} {cvj mcv : ConstantVal}
    (h : (checkProjLookups env' T ctorName lps nP nF i : CheckM _) =
      .ok (cvj, mcv)) :
    ∃ mval hmmcv,
      env'.find? ctorName = some (.ctorInfo cvj nP nF) ∧
      env'.find? (projModelName T i) = some (.defnInfo mcv mval hmmcv) ∧
      mcv.levelParams = lps ∧
      env'.find? (projFnName T i) = none ∧
      (env'.find? T).isSome = true ∧
      env'.find? eqName = some eqA := by
  simp only [checkProjLookups, Bind.bind, Except.bind] at h
  revert h
  match hctor : env'.find? ctorName with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.ctorInfo cvj' cnP cnF) => ?_
  intro h
  dsimp only at h
  by_cases hpp : cnP = nP ∧ cnF = nF
  case neg => rw [if_neg hpp] at h; exact nomatch h
  rw [if_pos hpp] at h
  obtain ⟨rfl, rfl⟩ := hpp
  try dsimp only at h
  revert h
  match hfm : env'.find? (projModelName T i) with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.defnInfo mcv' mval hmv') => ?_
  intro h
  dsimp only at h
  by_cases hmlps : mcv'.levelParams = lps
  case neg => rw [if_neg hmlps] at h; exact nomatch h
  rw [if_pos hmlps] at h
  try dsimp only at h
  by_cases hpn : (env'.find? (projFnName T i)).isNone = true
  case neg => rw [if_neg hpn] at h; exact nomatch h
  rw [if_pos hpn] at h
  have hpnone : env'.find? (projFnName T i) = none := by
    revert hpn
    cases env'.find? (projFnName T i) <;> simp
  try dsimp only at h
  by_cases hTf : (env'.find? T).isSome = true
  case neg => rw [if_neg hTf] at h; exact nomatch h
  rw [if_pos hTf] at h
  try dsimp only at h
  by_cases heqf : env'.find? eqName = some eqA
  case neg => rw [if_neg heqf] at h; exact nomatch h
  rw [if_pos heqf] at h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨mval, hmv', rfl, rfl, hmlps, hpnone, hTf, heqf⟩

/-- Invert stage 2 of `checkProjFn` (the public projection type). -/
theorem checkProjTy_inv {env' : Env} {T ctorName : Name} {lps : List Name}
    {mty pty : Expr} {nP nF : Nat}
    (h : (checkProjTy env' T ctorName lps mty nP nF : CheckM _) =
      .ok pty) :
    pty = mty.renameConsts (projBack T ctorName nF) ∧
    pty.renameConsts (projFwd T ctorName nF) = mty ∧
    pty.constsResolve env' = true ∧
    pty.looseBVarsBounded 0 = true ∧
    pty.hasFvar = false ∧
    pty.allLevelParamsDefined lps = true ∧
    -- task #148 T6: the telescope guard, which `ProjFnR` records
    (pty.stripPis (nP + 1)).isSome = true := by
  simp only [checkProjTy, Bind.bind, Except.bind] at h
  by_cases hround : ((mty.renameConsts (projBack T ctorName nF)).renameConsts
      (projFwd T ctorName nF) == mty) = true
  case neg => rw [if_neg hround] at h; exact nomatch h
  rw [if_pos hround] at h
  try dsimp only at h
  by_cases hres : (mty.renameConsts (projBack T ctorName nF)).constsResolve
      env' = true
  case neg => rw [if_neg hres] at h; exact nomatch h
  rw [if_pos hres] at h
  try dsimp only at h
  by_cases hwf3 : ((mty.renameConsts
        (projBack T ctorName nF)).looseBVarsBounded 0 &&
      !(mty.renameConsts (projBack T ctorName nF)).hasFvar &&
      (mty.renameConsts (projBack T ctorName nF)).allLevelParamsDefined
        lps) = true
  case neg => rw [if_neg hwf3] at h; exact nomatch h
  rw [if_pos hwf3] at h
  simp only [Bool.and_eq_true] at hwf3
  obtain ⟨⟨hptyb, hptyf'⟩, hptylp⟩ := hwf3
  have hptyf : (mty.renameConsts (projBack T ctorName nF)).hasFvar
      = false := by
    revert hptyf'
    cases (mty.renameConsts (projBack T ctorName nF)).hasFvar <;> simp
  try dsimp only at h
  by_cases hpis : ((mty.renameConsts
      (projBack T ctorName nF)).stripPis (nP + 1)).isSome = true
  case neg => rw [if_neg hpis] at h; exact nomatch h
  rw [if_pos hpis] at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨rfl, eq_of_beq hround, hres, hptyb, hptyf, hptylp, hpis⟩

/-- Invert stage 3 of `checkProjFn` (the reduction rule). -/
theorem checkProjRule_inv {env' : Env} {pty : Expr} {cvj : ConstantVal}
    {lps : List Name} {nP nF i : Nat} {rhsA : Expr}
    (h : checkProjRule (fueledOps mode F) env' pty cvj lps nP nF i =
      .ok rhsA) :
    ∃ raw rbinders cbindersR cbody,
      Expr.pisToLams (nP + nF) cvj.type (.bvar (nF - 1 - i)) = some raw ∧
      raw.hasFvar = false ∧
      raw.looseBVarsBounded 0 = true ∧
      annotateCore mode env' F 0 raw = .ok rhsA ∧
      rhsA.allLevelParamsDefined lps = true ∧
      rhsA.constsResolve env' = true ∧
      rhsA.looseBVarsBounded 0 = true ∧
      rhsA.hasFvar = false ∧
      rhsA.stripLams (nP + nF) = some (rbinders, .bvar (nF - 1 - i)) ∧
      cvj.type.stripPis (nP + nF) = some (cbindersR, cbody) ∧
      domsMatchAux (fun _ e => e) rbinders cbindersR 0 0 (nP + nF)
        = true ∧
      ∃ fvsP rest0 cdomsP crestP xFvs crest2X ldoms lrestL,
        openPisAtFvars nP pty 0 = some (fvsP, rest0) ∧
        Expr.instPisAt fvsP cvj.type = some (cdomsP, crestP) ∧
        DefEqListOk mode F env' (nP + nF) (fvsP.map Expr.fvarTypeD) cdomsP ∧
        openPisAtFvars nF crestP nP = some (xFvs, crest2X) ∧
        Expr.instLamsAt (fvsP ++ xFvs) rhsA = some (ldoms, lrestL) ∧
        DefEqListOk mode F env' (nP + nF)
          ((fvsP ++ xFvs).map Expr.fvarTypeD) ldoms ∧
        ∃ rhsTy, inferTypeCore mode env' F 0 rhsA = .ok rhsTy := by
  simp only [checkProjRule, fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq,
    fueledOps_ensureSort, fueledOps_whnf, Bind.bind, Except.bind] at h
  revert h
  match hraw : Expr.pisToLams (nP + nF) cvj.type (.bvar (nF - 1 - i)) with
  | none => intro h; exact nomatch h
  | some raw => ?_
  intro h
  dsimp only at h
  by_cases hrawwf : (!raw.hasFvar && raw.looseBVarsBounded 0) = true
  case neg => rw [if_neg hrawwf] at h; exact nomatch h
  rw [if_pos hrawwf] at h
  simp only [Bool.and_eq_true] at hrawwf
  obtain ⟨hrawf', hrawb⟩ := hrawwf
  have hrawf : raw.hasFvar = false := by
    revert hrawf'
    cases raw.hasFvar <;> simp
  try dsimp only at h
  cases hann : annotateCore mode env' F 0 raw with
  | error e => rw [hann] at h; exact nomatch h
  | ok rhsA' => ?_
  rw [hann] at h
  try dsimp only at h
  by_cases hrwf : (rhsA'.allLevelParamsDefined lps &&
      rhsA'.constsResolve env' && rhsA'.looseBVarsBounded 0 &&
      !rhsA'.hasFvar) = true
  case neg => rw [if_neg hrwf] at h; exact nomatch h
  rw [if_pos hrwf] at h
  simp only [Bool.and_eq_true] at hrwf
  obtain ⟨⟨⟨hrlp, hrres⟩, hrb⟩, hrf'⟩ := hrwf
  have hrf : rhsA'.hasFvar = false := by
    revert hrf'
    cases rhsA'.hasFvar <;> simp
  try dsimp only at h
  revert h
  match hstripR : rhsA'.stripLams (nP + nF) with
  | none => intro h; exact nomatch h
  | some (rbinders, rrbody) => ?_
  intro h
  dsimp only at h
  by_cases hrrb : (rrbody == Expr.bvar (nF - 1 - i)) = true
  case neg => rw [if_neg hrrb] at h; exact nomatch h
  rw [if_pos hrrb] at h
  obtain rfl := eq_of_beq hrrb
  try dsimp only at h
  revert h
  match hC_strip : cvj.type.stripPis (nP + nF) with
  | none => intro h; exact nomatch h
  | some (cbindersR, cbody) => ?_
  intro h
  dsimp only at h
  by_cases hdomsB : domsMatchAux (fun _ e => e) rbinders cbindersR 0 0
      (nP + nF) = true
  case neg => rw [if_neg hdomsB] at h; exact nomatch h
  rw [if_pos hdomsB] at h
  try dsimp only at h
  revert h
  match hopenP : openPisAtFvars nP pty 0 with
  | none => intro h; exact nomatch h
  | some (fvsP, rest0) => ?_
  intro h
  try dsimp only at h
  revert h
  match hcinstP : Expr.instPisAt fvsP cvj.type with
  | none => intro h; exact nomatch h
  | some (cdomsP, crestP) => ?_
  intro h
  try dsimp only at h
  revert h
  cases hde1 : checkDefEqList (fueledOps mode F) env' (nP + nF)
      (fvsP.map Expr.fvarTypeD) cdomsP with
  | error e => intro h; exact nomatch h
  | ok u1 => ?_
  intro h
  try dsimp only at h
  revert h
  match hopenX : openPisAtFvars nF crestP nP with
  | none => intro h; exact nomatch h
  | some (xFvs, crest2X) => ?_
  intro h
  try dsimp only at h
  revert h
  match hlinst : Expr.instLamsAt (fvsP ++ xFvs) rhsA' with
  | none => intro h; exact nomatch h
  | some (ldoms, lrestL) => ?_
  intro h
  try dsimp only at h
  revert h
  cases hde2 : checkDefEqList (fueledOps mode F) env' (nP + nF)
      ((fvsP ++ xFvs).map Expr.fvarTypeD) ldoms with
  | error e => intro h; exact nomatch h
  | ok u2 => ?_
  intro h
  try dsimp only at h
  revert h
  cases hity : inferTypeCore mode env' F 0 rhsA' with
  | error e => intro h; exact nomatch h
  | ok rhsTy => ?_
  intro h
  simp only [Bind.bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at h
  subst h
  exact ⟨raw, rbinders, cbindersR, cbody, rfl, hrawf, hrawb, hann,
    hrlp, hrres, hrb, hrf, hstripR, rfl, hdomsB,
    fvsP, rest0, cdomsP, crestP, xFvs, crest2X, ldoms, lrestL,
    rfl, hcinstP, checkDefEqList_inv hde1, hopenX, hlinst,
    checkDefEqList_inv hde2, rhsTy, hity⟩

/-- Invert stage 4 of `checkProjFn` (the pinned iota statement).  The
type slot carries no syntactic pin (hygienic binder names and
dependent field types spelled through projections defeat any pin);
instead both equation sides carry definitional type certificates at
the opened telescope (task #100 stage 3), and the slot itself one
against the sort its `Eq.{ℓA}` names (task #146). -/
theorem checkProjIota_inv {env' : Env} {T ctorName : Name}
    {lps : List Name} {cvj : ConstantVal} {nP nF i : Nat} {u : Unit}
    (h : checkProjIota mode (fueledOps mode F) env' env' T ctorName lps cvj nP
      nF i = .ok u) :
    ∃ tcv tval sbinders cbindersR cbody tySlot ℓA,
      env'.find? ((projModelName T i).str "iota") =
        some (.thmInfo tcv tval) ∧
      tcv.levelParams = lps ∧
      cvj.type.stripPis (nP + nF) = some (cbindersR, cbody) ∧
      domsMatchAux (fun _ e => e.renameConsts (projFwd T ctorName nF))
        sbinders cbindersR 0 0 (nP + nF) = true ∧
      tcv.type.stripPis (nP + nF) = some (sbinders,
        .app (.app (.app (.const eqName [ℓA]) tySlot)
          (Expr.mkAppN (.const (projModelName T i) (lps.map .param))
            (((List.range nP).map fun k => Expr.bvar (nP + nF - 1 - k)) ++
             [Expr.mkAppN
               (.const (ctorName.str "_model")
                 (cvj.levelParams.map .param))
               (((List.range nP).map fun k =>
                   Expr.bvar (nP + nF - 1 - k)) ++
                ((List.range nF).map fun k =>
                  Expr.bvar (nF - 1 - k)))])))
          (.bvar (nF - 1 - i))) ∧
      (∃ fvsO sbodyO,
        openPisAtFvars (nP + nF) tcv.type 0 = some (fvsO, sbodyO) ∧
        (∃ tl, inferTypeCore mode env' F (nP + nF)
            (sbodyO.getAppArgs.getD 1 (.bvar 0)) = .ok tl ∧
          isDefEqCore mode env' F (nP + nF) tl
            (sbodyO.getAppArgs.getD 0 (.bvar 0)) = .ok true) ∧
        (∃ tr, inferTypeCore mode env' F (nP + nF)
            (sbodyO.getAppArgs.getD 2 (.bvar 0)) = .ok tr ∧
          isDefEqCore mode env' F (nP + nF) tr
            (sbodyO.getAppArgs.getD 0 (.bvar 0)) = .ok true) ∧
        -- task #146's slot-sort certification is a TT-lane check
        -- (task #147): delivered only at `mode.ttChecks`
        (mode.ttChecks = true →
          ∃ tα, inferTypeCore mode env' F (nP + nF)
            (sbodyO.getAppArgs.getD 0 (.bvar 0)) = .ok tα ∧
          isDefEqCore mode env' F (nP + nF) tα (Expr.sort ℓA) = .ok true)) := by
  simp only [checkProjIota, checkIotaSidesTy, unwrapOr,
    fueledOps_inferType, fueledOps_isDefEq, Bind.bind, Except.bind,
    pure, Except.pure] at h
  revert h
  match hthm : env'.find? ((projModelName T i).str "iota") with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.thmInfo tcv tval) => ?_
  intro h
  dsimp only at h
  by_cases htlps : tcv.levelParams = lps
  case neg => rw [if_neg htlps] at h; exact nomatch h
  rw [if_pos htlps] at h
  try dsimp only at h
  revert h
  match hS_strip : tcv.type.stripPis (nP + nF) with
  | none => intro h; exact nomatch h
  | some (sbinders, sbody) => ?_
  intro h
  dsimp only at h
  revert h
  match hC_strip : cvj.type.stripPis (nP + nF) with
  | none => intro h; exact nomatch h
  | some (cbindersR, cbody) => ?_
  intro h
  dsimp only at h
  by_cases hsdomsB : domsMatchAux
      (fun _ e => e.renameConsts (projFwd T ctorName nF))
      sbinders cbindersR 0 0 (nP + nF) = true
  case neg => rw [if_neg hsdomsB] at h; exact nomatch h
  rw [if_pos hsdomsB] at h
  try dsimp only at h
  cases sbody
  case bvar => exact nomatch h
  case fvar => exact nomatch h
  case sort => exact nomatch h
  case const => exact nomatch h
  case lam => exact nomatch h
  case forallE => exact nomatch h
  case letE => exact nomatch h
  case lit => exact nomatch h
  case proj => exact nomatch h
  rename_i sA rhsC
  cases sA
  case bvar => exact nomatch h
  case fvar => exact nomatch h
  case sort => exact nomatch h
  case const => exact nomatch h
  case lam => exact nomatch h
  case forallE => exact nomatch h
  case letE => exact nomatch h
  case lit => exact nomatch h
  case proj => exact nomatch h
  rename_i sB lhsC
  cases sB
  case bvar => exact nomatch h
  case fvar => exact nomatch h
  case sort => exact nomatch h
  case const => exact nomatch h
  case lam => exact nomatch h
  case forallE => exact nomatch h
  case letE => exact nomatch h
  case lit => exact nomatch h
  case proj => exact nomatch h
  rename_i sEq tySlot
  cases sEq
  case bvar => exact nomatch h
  case fvar => exact nomatch h
  case sort => exact nomatch h
  case app => exact nomatch h
  case lam => exact nomatch h
  case forallE => exact nomatch h
  case letE => exact nomatch h
  case lit => exact nomatch h
  case proj => exact nomatch h
  rename_i c ℓs
  cases ℓs
  case nil => exact nomatch h
  rename_i ℓA ℓtail
  cases ℓtail
  case cons => exact nomatch h
  try dsimp only at h
  by_cases hc : c = eqName
  case neg => rw [if_neg hc] at h; exact nomatch h
  rw [if_pos hc] at h
  subst hc
  try dsimp only at h
  by_cases hlhs : (lhsC == Expr.mkAppN
      (.const (projModelName T i) (lps.map .param))
      (((List.range nP).map fun k => Expr.bvar (nP + nF - 1 - k)) ++
       [Expr.mkAppN
         (.const (ctorName.str "_model") (cvj.levelParams.map .param))
         (((List.range nP).map fun k => Expr.bvar (nP + nF - 1 - k)) ++
          ((List.range nF).map fun k => Expr.bvar (nF - 1 - k)))])) = true
  case neg => rw [if_neg hlhs] at h; exact nomatch h
  rw [if_pos hlhs] at h
  obtain rfl := eq_of_beq hlhs
  try dsimp only at h
  by_cases hrhsC : (rhsC == Expr.bvar (nF - 1 - i)) = true
  case neg => rw [if_neg hrhsC] at h; exact nomatch h
  rw [if_pos hrhsC] at h
  obtain rfl := eq_of_beq hrhsC
  try dsimp only at h
  revert h
  match hopenO : openPisAtFvars (nP + nF) tcv.type 0 with
  | none => intro h; exact nomatch h
  | some (fvsO, sbodyO) => ?_
  intro h
  try dsimp only at h
  revert h
  cases htl : inferTypeCore mode env' F (nP + nF)
      (sbodyO.getAppArgs.getD 1 (.bvar 0)) with
  | error e => intro h; exact nomatch h
  | ok tl => ?_
  intro h
  try dsimp only at h
  revert h
  cases hdl : isDefEqCore mode env' F (nP + nF) tl
      (sbodyO.getAppArgs.getD 0 (.bvar 0)) with
  | error e => intro h; exact nomatch h
  | ok vl => ?_
  cases vl with
  | false => intro h; simp at h
  | true => ?_
  intro h
  try dsimp only at h
  revert h
  cases htr : inferTypeCore mode env' F (nP + nF)
      (sbodyO.getAppArgs.getD 2 (.bvar 0)) with
  | error e => intro h; exact nomatch h
  | ok tr => ?_
  intro h
  try dsimp only at h
  revert h
  cases hdr : isDefEqCore mode env' F (nP + nF) tr
      (sbodyO.getAppArgs.getD 0 (.bvar 0)) with
  | error e => intro h; exact nomatch h
  | ok vr => ?_
  cases vr with
  | false => intro h; simp at h
  | true => ?_
  intro h
  dsimp only [Expr.getAppFn, eqHeadLevel] at h
  try dsimp only at h
  -- task #147: the slot-sort certification is gated on the mode
  cases htt : mode.ttChecks with
  | false =>
    exact ⟨tcv, tval, sbinders, cbindersR, cbody, tySlot, ℓA,
      rfl, htlps, rfl, hsdomsB, hS_strip,
      ⟨fvsO, sbodyO, hopenO, ⟨tl, htl, hdl⟩, ⟨tr, htr, hdr⟩,
        fun hc => absurd hc (by simp [htt])⟩⟩
  | true => ?_
  rw [htt] at h
  simp only [if_true] at h
  revert h
  cases htα : inferTypeCore mode env' F (nP + nF)
      (sbodyO.getAppArgs.getD 0 (.bvar 0)) with
  | error e => intro h; exact nomatch h
  | ok tα => ?_
  intro h
  try dsimp only at h
  revert h
  cases hdα : isDefEqCore mode env' F (nP + nF) tα (Expr.sort ℓA) with
  | error e => intro h; exact nomatch h
  | ok vα => ?_
  cases vα with
  | false => intro h; simp at h
  | true => ?_
  intro h
  exact ⟨tcv, tval, sbinders, cbindersR, cbody, tySlot, ℓA,
    rfl, htlps, rfl, hsdomsB, hS_strip,
    ⟨fvsO, sbodyO, hopenO, ⟨tl, htl, hdl⟩, ⟨tr, htr, hdr⟩,
      fun _ => ⟨tα, htα, hdα⟩⟩⟩

/-- Invert a successful `checkProjShape` run. -/
theorem checkProjShape_inv {pty cty : Expr} {nP nF : Nat} {u : Unit}
    (h : (checkProjShape pty cty nP nF : CheckM Unit) = .ok u) :
    ∃ abinders arest cbindersR cbody,
      pty.stripPis nP = some (abinders, arest) ∧
      cty.stripPis (nP + nF) = some (cbindersR, cbody) ∧
      (∃ dN dus, cbody.getAppFn = Expr.const dN dus) ∧
      cbody.getAppArgs.length = nP := by
  simp only [checkProjShape, Bind.bind, Except.bind] at h
  revert h
  match hA : pty.stripPis nP with
  | none => intro h; exact nomatch h
  | some (abinders, arest) => ?_
  intro h
  try dsimp only at h
  revert h
  match hC : cty.stripPis (nP + nF) with
  | none => intro h; exact nomatch h
  | some (cbindersR, cbody) => ?_
  intro h
  try dsimp only at h
  split at h
  next hlen =>
    try dsimp only at h
    revert h
    match hfn : cbody.getAppFn with
    | .const dN dus =>
      intro h
      exact ⟨abinders, arest, cbindersR, cbody, rfl, rfl,
        ⟨dN, dus, hfn⟩, eq_of_beq hlen⟩
    | .bvar _ => intro h; exact nomatch h
    | .fvar _ _ => intro h; exact nomatch h
    | .sort _ => intro h; exact nomatch h
    | .app _ _ => intro h; exact nomatch h
    | .lam _ _ _ => intro h; exact nomatch h
    | .forallE _ _ _ => intro h; exact nomatch h
    | .letE _ _ _ => intro h; exact nomatch h
    | .lit _ => intro h; exact nomatch h
    | .proj _ _ _ => intro h; exact nomatch h
  next => exact nomatch h

/-- Invert a successful `checkProjFn` into its stages. -/
theorem checkProjFn_inv {env' env₁ : Env} {T ctorName : Name}
    {lps : List Name} {nP nF i : Nat}
    (h : checkProjFn mode (fueledOps mode F) env' T ctorName lps nP nF i = .ok env₁) :
    ∃ cvj mcv,
      (checkProjLookups env' T ctorName lps nP nF i : CheckM _) =
        .ok (cvj, mcv) ∧
      ∃ pty, (checkProjTy env' T ctorName lps mcv.type nP nF : CheckM _) =
        .ok pty ∧
      (∃ u : Unit, (checkProjShape pty cvj.type nP nF : CheckM _)
        = .ok u) ∧
      i < nF ∧
      ∃ rhsA, checkProjRule (fueledOps mode F) env' pty cvj lps nP nF i =
        .ok rhsA ∧
      (∃ u : Unit, checkProjIota mode (fueledOps mode F) env' env' T ctorName
        lps cvj nP nF i = .ok u) ∧
      env₁ = ⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
        [projFnRule env'.find? T ctorName pty nP nF i rhsA]
        :: env'.consts⟩ := by
  simp only [checkProjFn, fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq,
    fueledOps_ensureSort, fueledOps_whnf, Bind.bind, Except.bind] at h
  cases hlk : (checkProjLookups env' T ctorName lps nP nF i : CheckM _) with
  | error e => rw [hlk] at h; exact nomatch h
  | ok pr => ?_
  rw [hlk] at h
  obtain ⟨cvj, mcv⟩ := pr
  try dsimp only at h
  cases hty : (checkProjTy env' T ctorName lps mcv.type nP nF : CheckM _) with
  | error e => rw [hty] at h; exact nomatch h
  | ok pty => ?_
  rw [hty] at h
  try dsimp only at h
  cases hshape : (checkProjShape pty cvj.type nP nF : CheckM Unit) with
  | error e => rw [hshape] at h; exact nomatch h
  | ok u0 => ?_
  rw [hshape] at h
  try dsimp only at h
  by_cases hi : i < nF
  case neg => rw [if_neg hi] at h; exact nomatch h
  rw [if_pos hi] at h
  try dsimp only at h
  cases hrule : checkProjRule (fueledOps mode F) env' pty cvj lps nP nF i
      with
  | error e => rw [hrule] at h; exact nomatch h
  | ok rhsA => ?_
  rw [hrule] at h
  try dsimp only at h
  cases hio : checkProjIota mode (fueledOps mode F) env' env' T ctorName lps
      cvj nP nF i with
  | error e => rw [hio] at h; exact nomatch h
  | ok u => ?_
  rw [hio] at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨cvj, mcv, rfl, pty, hty, ⟨u0, hshape⟩, hi, rhsA, hrule,
    ⟨u, hio⟩, h.symm⟩

/-- The projection-artifact phase adds only recursor-kind constants
(and only extends the environment). -/
theorem checkProjFold_find_new {T ctorName : Name} {lps : List Name}
    {nP nF : Nat} :
    ∀ (idxs : List Nat) (env' env₁ : Env),
    idxs.foldlM (installProjFnStep mode (fueledOps mode F) T ctorName lps nP nF)
      env' = .ok env₁ →
    ∀ (n : Name) (ci : ConstantInfo), env₁.find? n = some ci →
    env'.find? n = some ci ∨
      ∃ cv mI rP rules, ci = .recInfo cv mI rP rules
  | [], env', env₁, h, n, ci, hf => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact Or.inl hf
  | i₀ :: rest, env', env₁, h, n, ci, hf => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    unfold installProjFnStep at h
    by_cases hm : (env'.find? (projModelName T i₀)).isSome = true
    · rw [if_pos hm] at h
      cases hstep : checkProjFn mode (fueledOps mode F) env' T ctorName lps nP nF i₀ with
      | error e => rw [hstep] at h; exact nomatch h
      | ok env₂ => ?_
      rw [hstep] at h
      obtain ⟨cvj, mcv, hlk, pty, hty, hshape, hi, rhsA, hrule, hio,
        henv₂⟩ := checkProjFn_inv hstep
      have hcons : ∀ (n' : Name) (ci' : ConstantInfo),
          env₂.find? n' = some ci' →
          env'.find? n' = some ci' ∨
            ∃ cv mI rP rules, ci' = .recInfo cv mI rP rules := by
        intro n' ci' hf2
        rw [henv₂, Env.find?_cons] at hf2
        by_cases hh : (ConstantInfo.recInfo ⟨projFnName T i₀, lps, pty⟩
            nP nP [projFnRule env'.find? T ctorName pty nP nF i₀ rhsA]).name = n'
        · rw [if_pos hh] at hf2
          exact Or.inr ⟨_, _, _, _, (Option.some.inj hf2).symm⟩
        · rw [if_neg hh] at hf2
          exact Or.inl hf2
      rcases checkProjFold_find_new rest env₂ env₁ h n ci hf
        with hf' | hk
      · exact hcons n ci hf'
      · exact Or.inr hk
    · rw [if_neg hm] at h
      simp only [pure, Except.pure, Except.bind] at h
      exact checkProjFold_find_new rest env' env₁ h n ci hf

/-- The projection-artifact phase only extends the environment. -/
theorem checkProjFold_mono {T ctorName : Name} {lps : List Name}
    {nP nF : Nat} :
    ∀ (idxs : List Nat) (env' env₁ : Env),
    idxs.foldlM (installProjFnStep mode (fueledOps mode F) T ctorName lps nP nF)
      env' = .ok env₁ →
    ∀ n, (env'.find? n).isSome = true → (env₁.find? n).isSome = true
  | [], env', env₁, h, n, hn => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact hn
  | i₀ :: rest, env', env₁, h, n, hn => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    unfold installProjFnStep at h
    by_cases hm : (env'.find? (projModelName T i₀)).isSome = true
    · rw [if_pos hm] at h
      cases hstep : checkProjFn mode (fueledOps mode F) env' T ctorName lps nP nF i₀ with
      | error e => rw [hstep] at h; exact nomatch h
      | ok env₂ => ?_
      rw [hstep] at h
      obtain ⟨cvj, mcv, hlk, pty, hty, hshape, hi, rhsA, hrule, hio,
        henv₂⟩ := checkProjFn_inv hstep
      refine checkProjFold_mono rest env₂ env₁ h n ?_
      rw [henv₂, Env.find?_cons]
      by_cases hh : (ConstantInfo.recInfo ⟨projFnName T i₀, lps, pty⟩
          nP nP [projFnRule env'.find? T ctorName pty nP nF i₀ rhsA]).name = n
      · rw [if_pos hh]
        rfl
      · rw [if_neg hh]
        exact hn
    · rw [if_neg hm] at h
      simp only [pure, Except.pure, Except.bind] at h
      exact checkProjFold_mono rest env' env₁ h n hn

/-- The projection-artifact phase preserves stored lookups exactly
(every install is fresh). -/
theorem checkProjFold_find_preserved {T ctorName : Name}
    {lps : List Name} {nP nF : Nat} :
    ∀ (idxs : List Nat) (env' env₁ : Env),
    idxs.foldlM (installProjFnStep mode (fueledOps mode F) T ctorName lps nP nF)
      env' = .ok env₁ →
    ∀ (n : Name) (ci : ConstantInfo), env'.find? n = some ci →
    env₁.find? n = some ci
  | [], env', env₁, h, n, ci, hf => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact hf
  | i₀ :: rest, env', env₁, h, n, ci, hf => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    unfold installProjFnStep at h
    by_cases hm : (env'.find? (projModelName T i₀)).isSome = true
    · rw [if_pos hm] at h
      cases hstep : checkProjFn mode (fueledOps mode F) env' T ctorName lps nP nF i₀ with
      | error e => rw [hstep] at h; exact nomatch h
      | ok env₂ => ?_
      rw [hstep] at h
      obtain ⟨cvj, mcv, hlk, pty, hty, hshape, hi, rhsA, hrule, hio,
        henv₂⟩ := checkProjFn_inv hstep
      obtain ⟨mval2, hmmcv2, hctor2, hfm2, hmlps2, hpnone2, hTf2,
        heqf2⟩ := checkProjLookups_inv hlk
      refine checkProjFold_find_preserved rest env₂ env₁ h n ci ?_
      rw [henv₂]
      rw [Env.find?_cons_of_isSome
        (show env'.find? (ConstantInfo.recInfo
          ⟨projFnName T i₀, lps, pty⟩ nP nP
          [projFnRule env'.find? T ctorName pty nP nF i₀ rhsA]).name
            = none from hpnone2)
        (by rw [hf]; rfl)]
      exact hf
    · rw [if_neg hm] at h
      simp only [pure, Except.pure, Except.bind] at h
      exact checkProjFold_find_preserved rest env' env₁ h n ci hf

end ConLeche
