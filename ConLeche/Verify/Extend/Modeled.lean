module

public import ConLeche.Verify.Extend.Iota
import ConLeche.Verify.EnvWF

public section

/-!
# Modeled

The `checkMemberVal` / `checkIndMember` / `provisionRecs` inversions
that feed the member extension.

Every statement is over `Env`/`Expr` alone; the extension lemmas that
carry a valuation are stated one tier up, against these inversions.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

variable {mode : CheckMode}

open Expr

/-- Invert a successful `checkMemberVal` run. -/
theorem checkMemberVal_inv {blockNames : List Name} {env' : Env}
    {cv cvA : ConstantVal}
    (h : checkMemberVal (fueledOps mode F) blockNames env' cv = .ok cvA) :
    checkConstantVal (fueledOps mode F) env' cv = .ok cvA ∧
    cvA.name.isModelSuffix = false ∧
    ∃ cvm mval hmcvm,
      env'.find? (cvA.name.str "_model") =
        some (.defnInfo cvm mval hmcvm) ∧
      cvm.levelParams = cvA.levelParams ∧
      ((cvA.type.renameConsts (fun n =>
        if blockNames.contains n then n.str "_model" else n)) == cvm.type) =
        true := by
  simp only [checkMemberVal, fueledOps_annotate, fueledOps_inferType,
    fueledOps_isDefEq, fueledOps_ensureSort, fueledOps_whnf, Bind.bind,
    Except.bind] at h
  cases hccv : checkConstantVal (fueledOps mode F) env' cv with
  | error e => rw [hccv] at h; exact nomatch h
  | ok cvA' =>
  rw [hccv] at h
  try dsimp only at h
  by_cases hms : cvA'.name.isModelSuffix = true
  case pos => rw [if_pos hms] at h; exact nomatch h
  rw [if_neg hms] at h
  have hmsF : cvA'.name.isModelSuffix = false := by
    revert hms; cases cvA'.name.isModelSuffix <;> simp
  try dsimp only at h
  revert h
  match hfm : env'.find? (cvA'.name.str "_model") with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.defnInfo cvm mval hmcvm) => ?_
  intro h
  dsimp only at h
  by_cases hlps : cvm.levelParams = cvA'.levelParams
  case neg => rw [if_neg hlps] at h; exact nomatch h
  rw [if_pos hlps] at h
  try dsimp only at h
  by_cases hren : ((cvA'.type.renameConsts (fun n =>
      if blockNames.contains n then n.str "_model" else n)) == cvm.type)
      = true
  case neg => rw [if_neg hren] at h; exact nomatch h
  rw [if_pos hren] at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨rfl, hmsF, cvm, mval, hmcvm, hfm, hlps, hren⟩

/-- Invert a successful `checkIndMember` run (non-recursor members). -/
theorem checkIndMember_inv {blockNames : List Name} {caps : IndCaps}
    {env' env₁ : Env} {ci : ConstantInfo}
    (h : checkIndMember (fueledOps mode F) blockNames caps env' ci = .ok env₁) :
    ∃ cvA cvm mval hmcvm,
      checkConstantVal (fueledOps mode F) env' ci.toConstantVal = .ok cvA ∧
      cvA.name.isModelSuffix = false ∧
      env'.find? (cvA.name.str "_model") = some (.defnInfo cvm mval hmcvm) ∧
      cvm.levelParams = cvA.levelParams ∧
      ((cvA.type.renameConsts (fun n =>
        if blockNames.contains n then n.str "_model" else n)) == cvm.type) =
        true ∧
      ((∃ cv caps', ci = .indInfo cv caps') ∧
         env₁ = ⟨.indInfo cvA caps :: env'.consts⟩ ∨
       (∃ cv nP nF, ci = .ctorInfo cv nP nF ∧
         env₁ = ⟨.ctorInfo cvA nP nF :: env'.consts⟩)) := by
  simp only [checkIndMember, Bind.bind, Except.bind] at h
  cases hcmv : checkMemberVal (fueledOps mode F) blockNames env'
      ci.toConstantVal with
  | error e => rw [hcmv] at h; exact nomatch h
  | ok cvA =>
  rw [hcmv] at h
  obtain ⟨hccv, hms, cvm, mval, hmcvm, hfm, hlps, hren⟩ :=
    checkMemberVal_inv hcmv
  refine ⟨cvA, cvm, mval, hmcvm, hccv, hms, hfm, hlps, hren, ?_⟩
  cases ci with
  | axiomInfo cv => exact nomatch h
  | projInfo _ => exact nomatch h
  | defnInfo cv value hint => exact nomatch h
  | thmInfo cv value => exact nomatch h
  | recInfo cv mI rP rules => exact nomatch h
  | indInfo cv caps' =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl ⟨⟨cv, caps', rfl⟩, h.symm⟩
  | ctorInfo cv nP nF =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inr ⟨cv, nP, nF, rfl, h.symm⟩

/-- One step of `provisionRecs`. -/
theorem provisionRecs_cons_inv {blockNames : List Name}
    {envAcc : Env} {ci : ConstantInfo} {rest : List ConstantInfo}
    {p : Env × List (ConstantVal × Nat × Nat × List RecRule)}
    (h : provisionRecs (fueledOps mode F) blockNames envAcc (ci :: rest) =
      .ok p) :
    ∃ cv mI rP rules cvA p',
      ci = .recInfo cv mI rP rules ∧
      checkMemberVal (fueledOps mode F) blockNames envAcc ci.toConstantVal =
        .ok cvA ∧
      provisionRecs (fueledOps mode F) blockNames
        ⟨.recInfo cvA mI rP [] :: envAcc.consts⟩ rest = .ok p' ∧
      p = (p'.1, (cvA, mI, rP, rules) :: p'.2) := by
  revert h
  match ci with
  | .recInfo cv mI rP rules => ?_
  | .axiomInfo _ => intro h; exact nomatch h
  | .projInfo _ => intro h; exact nomatch h
  | .defnInfo _ _ _ => intro h; exact nomatch h
  | .thmInfo _ _ => intro h; exact nomatch h
  | .indInfo _ _ => intro h; exact nomatch h
  | .ctorInfo _ _ _ => intro h; exact nomatch h
  intro h
  simp only [provisionRecs, Bind.bind, Except.bind] at h
  cases hcmv : checkMemberVal (fueledOps mode F) blockNames envAcc
      (ConstantInfo.recInfo cv mI rP rules).toConstantVal with
  | error e => rw [hcmv] at h; exact nomatch h
  | ok cvA =>
  rw [hcmv] at h
  try dsimp only at h
  cases hrec : provisionRecs (fueledOps mode F) blockNames
      ⟨.recInfo cvA mI rP [] :: envAcc.consts⟩ rest with
  | error e => rw [hrec] at h; exact nomatch h
  | ok p' =>
  rw [hrec] at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨cv, mI, rP, rules, cvA, p', rfl, rfl, hrec, h.symm⟩

end ConLeche
