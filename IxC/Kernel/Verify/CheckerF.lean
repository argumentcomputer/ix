module

import IxC.Kernel.Verify.FastOps
public import IxC.Kernel.Verify.EnvBound
import IxC.Kernel.Inductives.SumInstallF
public import IxC.Kernel.Inductives.NativeInstallF

public section

/-!
# The indexed checker mirrors agree with the generic checker (task #63)

Under `mkFEnv` every `F`-mirror of `IxC/Kernel/CheckerS.lean` *is*
its `IxC/Kernel/Checker.lean` counterpart: the mirrors differ only
in pure lookup subterms (`FEnv.find?` for `Env.find?`,
`Expr.constsResolveF` for `Expr.constsResolve`, and the compound
guards built from them), each of which `mkFEnv_find?` rewrites away.
Environment-*extending* mirrors (`checkDefnValF` …) return the pushed
index and are related run-wise by the cached tier's bridge
(`IxC/Kernel/Verify/Cached/BridgeCS4.lean`) — here only the value-level
pieces are proven equal.
-/

namespace Ix.Kernel

/-- `FEnv.find?` under `mkFEnv`, as a function equation. -/
theorem mkFEnv_find?_fun (env : Env md) :
    FEnv.find? (mkFEnv env) = env.find? :=
  funext (mkFEnv_find? env)


theorem mkFEnv_env (env : Env md) : (mkFEnv env).env = env := rfl

variable {mode : CheckMode}
variable {ev : Evidences md}

theorem mkFEnv_findCV? (env : Env md) (n : Key md) :
    (mkFEnv env).findCV? n = env.findCV? n := by
  simp only [FEnv.findCV?, Env.findCV?, mkFEnv_find?] <;> rfl

theorem constsResolveF_eq (env : Env md) :
    ∀ (e : Expr md), e.constsResolveF (mkFEnv env) = e.constsResolve env
  | .bvar _ | .sort _ => rfl
  | .lit (.natVal _) => by
    simp only [Expr.constsResolveF, Expr.constsResolve, mkFEnv_find?]
  | .lit (.strVal _) => by
    simp only [Expr.constsResolveF, Expr.constsResolve, mkFEnv_find?]
  | .const n _ => by
    simp only [Expr.constsResolveF, Expr.constsResolve, mkFEnv_find?]
  | .fvar _ ty => by
    simp only [Expr.constsResolveF, Expr.constsResolve,
      constsResolveF_eq env ty]
  | .app f a => by
    simp only [Expr.constsResolveF, Expr.constsResolve,
      constsResolveF_eq env f, constsResolveF_eq env a]
  | .lam ty body _ => by
    simp only [Expr.constsResolveF, Expr.constsResolve,
      constsResolveF_eq env ty, constsResolveF_eq env body]
  | .forallE ty body _ => by
    simp only [Expr.constsResolveF, Expr.constsResolve,
      constsResolveF_eq env ty, constsResolveF_eq env body]
  | .letE ty val body _ => by
    simp only [Expr.constsResolveF, Expr.constsResolve,
      constsResolveF_eq env ty, constsResolveF_eq env val,
      constsResolveF_eq env body]
  | .proj s _ e => by
    simp only [Expr.constsResolveF, Expr.constsResolve, mkFEnv_find?,
      constsResolveF_eq env e]

/-- `constsResolveF` under `mkFEnv`, as a function equation. -/
theorem constsResolveF_eq_fun (env : Env md) :
    (Expr.constsResolveF (mkFEnv env)) = (Expr.constsResolve env ·) :=
  funext (constsResolveF_eq env)

theorem natOpCodF_eq (env : Env md) (c : Key md) (e : Expr md) :
    natOpCodF (mkFEnv env) c e = natOpCod env c e := by
  simp only [natOpCodF, natOpCod, mkFEnv_find?] <;> rfl

theorem natOpTyPinnedF_eq (env : Env md) (c : Key md) (ty : Expr md) :
    natOpTyPinnedF (mkFEnv env) c ty = natOpTyPinned env c ty := by
  simp only [natOpTyPinnedF, natOpTyPinned, natOpCodF_eq] <;> rfl

theorem natOpStoredOkF_eq (env : Env md) (n : Key md) :
    natOpStoredOkF (mkFEnv env) n = natOpStoredOk env n := by
  simp only [natOpStoredOkF, natOpStoredOk, mkFEnv_find?,
    natOpTyPinnedF_eq] <;> rfl

theorem stdAxiomOkF_eq (env : Env md) (cvA : ConstantVal md) :
    stdAxiomOkF (mkFEnv env) cvA = stdAxiomOk env cvA := by
  simp only [stdAxiomOkF, stdAxiomOk, mkFEnv_find?] <;> rfl

theorem trustCompilerOkF_eq (env : Env md) (cvA : ConstantVal md) :
    trustCompilerOkF (mkFEnv env) cvA = trustCompilerOk env cvA := by
  simp only [trustCompilerOkF, trustCompilerOk, mkFEnv_find?] <;> rfl

theorem reduceStoredOkF_eq (env : Env md) (c : Key md) :
    reduceStoredOkF (mkFEnv env) c = reduceStoredOk env c := by
  simp only [reduceStoredOkF, reduceStoredOk, mkFEnv_find?] <;> rfl

theorem reduceElemOkF_eq (env : Env md) (c : Key md) :
    reduceElemOkF (mkFEnv env) c = reduceElemOk env c := by
  simp only [reduceElemOkF, reduceElemOk, mkFEnv_find?] <;> rfl

theorem ofReduceAxOkF_eq (env : Env md) (cvA : ConstantVal md) :
    ofReduceAxOkF (mkFEnv env) cvA = ofReduceAxOk env cvA := by
  simp only [ofReduceAxOkF, ofReduceAxOk, mkFEnv_find?,
    reduceElemOkF_eq, reduceStoredOkF_eq] <;> rfl

theorem natOpStoredOkF_eq_fun (env : Env md) :
    natOpStoredOkF (mkFEnv env) = natOpStoredOk env :=
  funext (natOpStoredOkF_eq env)

theorem divModEnvGuardF_eq (env : Env md) (c : Key md) :
    divModEnvGuardF (mkFEnv env) c = divModEnvGuard env c := by
  simp only [divModEnvGuardF, divModEnvGuard, mkFEnv_find?,
    natOpGuardF_eq, natOpStoredOkF_eq_fun] <;> rfl

theorem divModCertGuardF_eq (env : Env md) (c : Key md) (annVal : Expr md)
    (hyps : List (Expr md)) (eqE proof : Expr md) :
    divModCertGuardF (mkFEnv env) c annVal hyps eqE proof
      = divModCertGuard env c annVal hyps eqE proof := by
  simp only [divModCertGuardF, divModCertGuard, constsResolveF_eq] <;> rfl

theorem divModCertsGuardF_eq (proofs : List (Expr md)) (env : Env md) (c : Key md)
    (annVal : Expr md) :
    divModCertsGuardF proofs (mkFEnv env) c annVal
      = divModCertsGuard proofs env c annVal := by
  simp only [divModCertsGuardF, divModCertsGuard, divModCertGuardF_eq] <;> rfl

theorem checkEtaThmF_eq (env : Env md) (T ctorName : Key md)
    (lps : List LevelParam) (nP nF : Nat) :
    checkEtaThmF mode (mkFEnv env) T ctorName lps nP nF
      = checkEtaThm mode env T ctorName lps nP nF := by
  simp only [checkEtaThmF, checkEtaThm, mkFEnv_find?] <;> rfl

theorem checkUnitThmF_eq (env : Env md) (T : Key md) (lps : List LevelParam)
    (nP : Nat) :
    checkUnitThmF mode (mkFEnv env) T lps nP = checkUnitThm mode env T lps nP := by
  simp only [checkUnitThmF, checkUnitThm, mkFEnv_find?] <;> rfl

theorem indBlockCapsF_eq (env : Env md) (cvT cvC : ConstantVal md)
    (nP nF : Nat) :
    indBlockCapsF mode (mkFEnv env) cvT cvC nP nF
      = indBlockCaps mode env cvT cvC nP nF := by
  simp only [indBlockCapsF, indBlockCaps, checkEtaThmF_eq,
    checkUnitThmF_eq] <;> rfl

theorem ctorResidualOkF_eq (env : Env md) (T ctorName : Key md)
    (lps : List LevelParam) (nP nF : Nat) (eta : Bool) :
    ctorResidualOkF mode (mkFEnv env) T ctorName lps nP nF eta
      = ctorResidualOk mode env T ctorName lps nP nF eta := by
  simp only [ctorResidualOkF, ctorResidualOk, mkFEnv_find?] <;> rfl

theorem nestedRuleShapeF_eq (env' envS : Env md) (cvName : Key md)
    (lps : List LevelParam) (tyA : Expr md) (mI rP cnP j : Nat) :
    nestedRuleShapeF (mkFEnv env') (mkFEnv envS) cvName lps tyA
        mI rP cnP j
      = nestedRuleShape env' envS cvName lps tyA mI rP cnP j := by
  simp only [nestedRuleShapeF, nestedRuleShape, mkFEnv_findCV?,
    constsResolveF_eq] <;> rfl

/-! ## Monadic mirrors (non-extending: plain program equalities) -/

section Monadic

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

theorem checkConstantValF_eq (ops : (CheckerOps md) m) (env : Env md)
    (cv : ConstantVal md) :
    checkConstantValF ops (mkFEnv env) cv = checkConstantVal ops env cv := by
  simp only [checkConstantValF, checkConstantVal, mkFEnv_find?,
    constsResolveF_eq] <;> rfl

theorem checkMemberValF_eq (ops : (CheckerOps md) m) (blockNames : List (Key md))
    (env : Env md) (cv : ConstantVal md) :
    checkMemberValF ops blockNames (mkFEnv env) cv
      = checkMemberVal ops blockNames env cv := by
  simp only [checkMemberValF, checkMemberVal, mkFEnv_find?,
    checkConstantValF_eq] <;> rfl

theorem checkIotaThmF_eq (ops : (CheckerOps md) m) (env' envS : Env md)
    (f : Key md → Key md) (cvName : Key md) (lps : List LevelParam) (tyA : Expr md)
    (mI rP j : Nat) (r : RecRule md) (cvj : ConstantVal md)
    (cnP cnF : Nat) (rhsA : Expr md) :
    checkIotaThmF mode ops (mkFEnv env') (mkFEnv envS) f cvName lps tyA
        mI rP j r cvj cnP cnF rhsA
      = checkIotaThm mode ops env' envS f cvName lps tyA
        mI rP j r cvj cnP cnF rhsA := by
  simp only [checkIotaThmF, checkIotaThm, mkFEnv_findCV?] <;> rfl

theorem checkIotaThmNF_eq (ops : (CheckerOps md) m) (env' envS : Env md)
    (f : Key md → Key md) (cvName : Key md) (lps : List LevelParam) (tyA : Expr md)
    (mI rP j : Nat) (r : RecRule md) (cvj : ConstantVal md)
    (cnP cnF : Nat) (rhsA : Expr md) :
    checkIotaThmNF mode ops (mkFEnv env') (mkFEnv envS) f cvName lps tyA
        mI rP j r cvj cnP cnF rhsA
      = checkIotaThmN mode ops env' envS f cvName lps tyA
        mI rP j r cvj cnP cnF rhsA := by
  simp only [checkIotaThmNF, checkIotaThmN, mkFEnv_findCV?,
    nestedRuleShapeF_eq] <;> rfl

theorem checkIotaRuleF_eq (ops : (CheckerOps md) m) (env' envS : Env md)
    (f : Key md → Key md) (cvName : Key md) (lps : List LevelParam) (tyA : Expr md)
    (mI rP j : Nat) (r : RecRule md) :
    checkIotaRuleF mode ops (mkFEnv env') (mkFEnv envS) f cvName lps tyA
        mI rP j r
      = checkIotaRule mode ops env' envS f cvName lps tyA mI rP j r := by
  simp only [checkIotaRuleF, checkIotaRule, mkFEnv_find?, mkFEnv_find?_fun,
    constsResolveF_eq, checkIotaThmF_eq, checkIotaThmNF_eq] <;> rfl

theorem checkIotaRulesF_eq (ops : (CheckerOps md) m) (env' envS : Env md)
    (f : Key md → Key md) (cvName : Key md) (lps : List LevelParam) (tyA : Expr md)
    (mI rP : Nat) :
    ∀ (j : Nat) (rs : List (RecRule md)),
      checkIotaRulesF mode ops (mkFEnv env') (mkFEnv envS) f cvName lps tyA
          mI rP j rs
        = checkIotaRules mode ops env' envS f cvName lps tyA mI rP j rs
  | _, [] => rfl
  | j, r :: rest => by
    simp only [checkIotaRulesF, checkIotaRules, checkIotaRuleF_eq,
      checkIotaRulesF_eq ops env' envS f cvName lps tyA mI rP
        (j + 1) rest]

theorem checkProjLookupsF_eq (env : Env md) (T ctorName : Key md)
    (lps : List LevelParam) (nP nF i : Nat) :
    (checkProjLookupsF (mkFEnv env) T ctorName lps nP nF i : m _)
      = checkProjLookups env T ctorName lps nP nF i := by
  simp only [checkProjLookupsF, checkProjLookups, mkFEnv_find?] <;> rfl

theorem checkProjTyF_eq (env : Env md) (T ctorName : Key md)
    (lps : List LevelParam) (mty : Expr md) (nP nF : Nat) :
    (checkProjTyF (mkFEnv env) T ctorName lps mty nP nF : m _)
      = checkProjTy env T ctorName lps mty nP nF := by
  simp only [checkProjTyF, checkProjTy, constsResolveF_eq] <;> rfl

theorem checkProjRuleF_eq (ops : (CheckerOps md) m) (env : Env md) (pty : Expr md)
    (cvj : ConstantVal md) (lps : List LevelParam) (nP nF i : Nat) :
    checkProjRuleF ops (mkFEnv env) pty cvj lps nP nF i
      = checkProjRule ops env pty cvj lps nP nF i := by
  simp only [checkProjRuleF, checkProjRule, constsResolveF_eq,
    domsMatchAuxA_eq, openPisAtFvarsF_eq, instPisAtF_eq,
    instLamsAtF_eq] <;> rfl

theorem checkProjIotaF_eq (ops : (CheckerOps md) m) (env : Env md)
    (T ctorName : Key md)
    (lps : List LevelParam) (cvj : ConstantVal md) (nP nF i : Nat) :
    checkProjIotaF mode ops (mkFEnv env) T ctorName lps cvj nP nF i
      = checkProjIota mode ops env env T ctorName lps cvj nP nF i := by
  simp only [checkProjIotaF, checkProjIota, mkFEnv_find?, mkFEnv_env]
    <;> rfl

/-! ### The direct simple-structure path (task #82) -/

theorem checkStructDomsAtF_eq (ops : (CheckerOps md) m) (env : Env md)
    (off : Nat) (fvs doms : List (Expr md)) :
    ∀ (j : Nat),
      checkStructDomsAtF ops (mkFEnv env) off fvs doms j
        = checkStructDomsAt ops env off fvs doms j
  | 0 => rfl
  | j + 1 => by
    simp only [checkStructDomsAtF, checkStructDomsAt, mkFEnv_env,
      checkStructDomsAtF_eq ops env off fvs doms j]

/-! ### The direct sum path (task #175 sum-types, indexed) -/

/-- `checkStructFieldSortsIF` (task #175 indexed) at `mkFEnv`. -/
theorem checkStructFieldSortsIF_eq (ops : (CheckerOps md) m) (env : Env md)
    (isProp large : Bool) (s : Level) (nP : Nat) (fvs idxArgs : List (Expr md)) :
    ∀ (j : Nat),
      checkStructFieldSortsIF ops (mkFEnv env) isProp large s nP fvs idxArgs j
        = checkStructFieldSortsI ops env isProp large s nP fvs idxArgs j
  | 0 => rfl
  | j + 1 => by
    simp only [checkStructFieldSortsIF, checkStructFieldSortsI, mkFEnv_env,
      checkStructFieldSortsIF_eq ops env isProp large s nP fvs idxArgs j]

/-- `checkStructFieldSortsIFA` (task #175 indexed) at `List.toArray`. -/
theorem checkStructFieldSortsIFA_eq (ops : (CheckerOps md) m) (fe : FEnv md)
    (isProp large : Bool) (s : Level) (nP : Nat) (fvs idxArgs : List (Expr md)) :
    ∀ j, checkStructFieldSortsIFA ops fe isProp large s nP fvs.toArray idxArgs j
      = checkStructFieldSortsIF ops fe isProp large s nP fvs idxArgs j
  | 0 => rfl
  | j + 1 => by
    simp only [checkStructFieldSortsIFA, checkStructFieldSortsIF,
      List.getElem?_toArray,
      checkStructFieldSortsIFA_eq ops fe isProp large s nP fvs idxArgs j]

theorem normCtorValF_eq (ops : (CheckerOps md) m) (env : Env md) (T : Key md) (nP nF : Nat)
    (cvC cvCa : ConstantVal md) :
    normCtorValF ops (mkFEnv env) T nP nF cvC cvCa = normCtorVal ops env T nP nF cvC cvCa := by
  simp only [normCtorValF, normCtorVal, mkFEnv_env, checkConstantValF_eq]

theorem checkSumCtorF_eq (ops : (CheckerOps md) m) (env₀ env : Env md) (T : Key md)
    (lps : List LevelParam) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (cvC : ConstantVal md) (nF : Nat) (cvTa : ConstantVal md) :
    checkSumCtorF ops (mkFEnv env₀) (mkFEnv env) T lps nP nIdx resSort isProp
        large cvC nF cvTa
      = checkSumCtor ops env₀ env T lps nP nIdx resSort isProp large cvC nF
        cvTa := by
  simp only [checkSumCtorF, checkSumCtor, checkConstantValF_eq, normCtorValF_eq,
    checkStructDomsAtFA_eq, checkStructDomsAtF_eq, openPisAtFvarsF_eq,
    checkStructFieldSortsIFA_eq, checkStructFieldSortsIF_eq, constsResolveF_eq]

theorem checkSumCtorsF_eq (ops : (CheckerOps md) m) (env₀ env : Env md) (T : Key md)
    (lps : List LevelParam) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (cvTa : ConstantVal md) :
    ∀ (cs : List (ConstantVal md × Nat)),
      checkSumCtorsF ops (mkFEnv env₀) (mkFEnv env) T lps nP nIdx resSort isProp
          large cvTa cs
        = checkSumCtors ops env₀ env T lps nP nIdx resSort isProp large cvTa cs
  | [] => rfl
  | c :: cs => by
    simp only [checkSumCtorsF, checkSumCtors, checkSumCtorF_eq,
      checkSumCtorsF_eq ops env₀ env T lps nP nIdx resSort isProp large cvTa cs]

omit [MonadExceptOf CheckError m] in
theorem checkDivModCertsF_eq (ops : (CheckerOps md) m) (env : Env md) (c : Key md)
    (annVal : Expr md) :
    ∀ (stmts : List (List (Expr md) × Expr md)) (proofs : List (Expr md)),
      checkDivModCertsF ops (mkFEnv env) c annVal stmts proofs
        = checkDivModCerts ops env c annVal stmts proofs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | (_, _) :: _, [] => rfl
  | (hyps, eqE) :: srest, proof :: prest => by
    simp only [checkDivModCertsF, checkDivModCerts, divModCertGuardF_eq,
      mkFEnv_env, checkDivModCertsF_eq ops env c annVal srest prest]

theorem checkDivModEvidenceF_eq (ops : (CheckerOps md) m) (env env2 : Env md)
    (c : Key md) :
    checkDivModEvidenceF ops ev (mkFEnv env) (mkFEnv env2) c
      = checkDivModEvidence ops ev env env2 c := by
  simp only [checkDivModEvidenceF, checkDivModEvidence, mkFEnv_find?, mkFEnv_find?_fun,
    divModEnvGuardF_eq, divModCertsGuardF_eq, checkDivModCertsF_eq] <;> rfl

theorem checkReduceIdentityF_eq (ops : (CheckerOps md) m) (env env2 : Env md)
    (c : Key md) (value : Expr md) :
    checkReduceIdentityF ops (mkFEnv env) (mkFEnv env2) c value
      = checkReduceIdentity ops env env2 c value := by
  simp only [checkReduceIdentityF, checkReduceIdentity, mkFEnv_env,
    reduceStoredOkF_eq, reduceElemOkF_eq] <;> rfl

end Monadic

/-! ## Environment-extending mirrors: the push equation

Each extending mirror is its generic counterpart followed by `mkFEnv`
— the pushed index of the cons-extended environment *is* `mkFEnv` of
it.  The monadic `_push` equations that consume it are stated at the
executing monad, in `IxC/Kernel/Verify/Cached/BridgeCSDecl.lean`; the
`CheckIM` copies here went with the interned drivers (task #172). -/

theorem push_mkFEnv (env : Env md) (ci : ConstantInfo md) :
    (mkFEnv env).push ci = mkFEnv ⟨ci :: env.consts⟩ := rfl

/-- The direct sum's constructor conses through the index (task #175
sum-types): the pushed index of the consed environment *is* `mkFEnv`
of it. -/
theorem consSumCtorsF_mkFEnv (nP : Nat) :
    ∀ (cs : List (ConstantVal md × Nat)) (env : Env md),
      consSumCtorsF nP cs (mkFEnv env) = mkFEnv (consSumCtors nP cs env)
  | [], _ => rfl
  | c :: cs, env => by
    simp only [consSumCtorsF, consSumCtors, push_mkFEnv,
      consSumCtorsF_mkFEnv nP cs ⟨.ctorInfo c.1 nP c.2 :: env.consts⟩]

/-! ## The direct recursive install's mirrors (task #188) -/

section FixMirrors

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

theorem nativeOpenedOkF_eq (env₀ : Env md) (T : Key md) (lps : List LevelParam) (nP nIdx : Nat)
    (cty : Expr md) (nF : Nat) (ks : List RecFieldKind) :
    nativeOpenedOkF .plain (mkFEnv env₀) T lps nP nIdx cty nF ks
      = nativeOpenedOk env₀ T lps nP nIdx cty nF ks := by
  simp only [nativeOpenedOkF, nativeOpenedOk, StructWalkers.plain, constsResolveF_eq]
    <;> rfl

theorem nativeFieldsOkF_eq (env₀ : Env md) (T : Key md) (lps : List LevelParam) (nP nIdx : Nat)
    (ctorsA : List (ConstantVal md × Nat)) (kinds : List (List RecFieldKind)) :
    nativeFieldsOkF .plain (mkFEnv env₀) T lps nP nIdx ctorsA kinds
      = nativeFieldsOk env₀ T lps nP nIdx ctorsA kinds := by
  simp only [nativeFieldsOkF, nativeFieldsOk, nativeOpenedOkF_eq] <;> rfl

theorem checkNativeRulesF_eq (envR : Env md) (rlps : List LevelParam) (T : Key md) (lps : List LevelParam)
    (elim : LevelParam) (large : Bool) (nP nIdx : Nat) (tty : Expr md)
    (ctors : List (Key md × Nat × Expr md × List Nat)) (recC : Key md) (rlvls : List Level) :
    ∀ (k j : Nat),
      checkNativeRulesF (m := m) .plain (mkFEnv envR) rlps T lps elim large nP nIdx tty ctors
          recC rlvls k j
        = checkNativeRules (m := m) envR rlps T lps elim large nP nIdx tty ctors recC
            rlvls k j
  | 0, _ => rfl
  | k + 1, j => by
    simp only [checkNativeRulesF, checkNativeRules,
      checkNativeRulesF_eq envR rlps T lps elim large nP nIdx tty ctors recC rlvls k
        (j + 1)]
    simp only [StructWalkers.plain, constsResolveF_eq]

theorem checkNativeRecF_eq (ops : (CheckerOps md) m) (env : Env md) (p : NativeParts md)
    (cvTa : ConstantVal md) (ctorsA : List (ConstantVal md × Nat)) :
    checkNativeRecF ops .plain (mkFEnv env) p cvTa ctorsA
      = checkNativeRec ops env p cvTa ctorsA := by
  simp only [checkNativeRecF, checkNativeRec, mkFEnv_env, checkConstantValF_eq,
    push_mkFEnv, checkNativeRulesF_eq]
  simp only [StructWalkers.plain, constsResolveF_eq]

end FixMirrors

end Ix.Kernel
