module

import ConLeche.Verify.FastOps
public import ConLeche.Verify.EnvBound
import ConLeche.Kernel.Inductives.SumInstallF
public import ConLeche.Kernel.Inductives.NativeInstallF

public section

/-!
# The indexed checker mirrors agree with the generic checker (task #63)

Under `mkFEnv` every `F`-mirror of `ConLeche/Kernel/CheckerS.lean` *is*
its `ConLeche/Kernel/Checker.lean` counterpart: the mirrors differ only
in pure lookup subterms (`FEnv.find?` for `Env.find?`,
`Expr.constsResolveF` for `Expr.constsResolve`, and the compound
guards built from them), each of which `mkFEnv_find?` rewrites away.
Environment-*extending* mirrors (`checkDefnValF` …) return the pushed
index and are related run-wise by the cached tier's bridge
(`ConLeche/Verify/Cached/BridgeCS4.lean`) — here only the value-level
pieces are proven equal.
-/

namespace ConLeche

/-- `FEnv.find?` under `mkFEnv`, as a function equation. -/
theorem mkFEnv_find?_fun (env : Env) :
    FEnv.find? (mkFEnv env) = env.find? :=
  funext (mkFEnv_find? env)


theorem mkFEnv_env (env : Env) : (mkFEnv env).env = env := rfl

variable {mode : CheckMode}
variable {pins : List NatOpPinSet}

theorem mkFEnv_findCV? (env : Env) (n : Name) :
    (mkFEnv env).findCV? n = env.findCV? n := by
  simp only [FEnv.findCV?, Env.findCV?, mkFEnv_find?] <;> rfl

theorem constsResolveF_eq (env : Env) :
    ∀ (e : Expr), e.constsResolveF (mkFEnv env) = e.constsResolve env
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
  | .letE ty val body => by
    simp only [Expr.constsResolveF, Expr.constsResolve,
      constsResolveF_eq env ty, constsResolveF_eq env val,
      constsResolveF_eq env body]
  | .proj s _ e => by
    simp only [Expr.constsResolveF, Expr.constsResolve, mkFEnv_find?,
      constsResolveF_eq env e]

/-- `constsResolveF` under `mkFEnv`, as a function equation. -/
theorem constsResolveF_eq_fun (env : Env) :
    (Expr.constsResolveF (mkFEnv env)) = (Expr.constsResolve env ·) :=
  funext (constsResolveF_eq env)

theorem natOpCodF_eq (env : Env) (c : Name) (e : Expr) :
    natOpCodF (mkFEnv env) c e = natOpCod env c e := by
  simp only [natOpCodF, natOpCod, mkFEnv_find?] <;> rfl

theorem natOpTyPinnedF_eq (env : Env) (c : Name) (ty : Expr) :
    natOpTyPinnedF (mkFEnv env) c ty = natOpTyPinned env c ty := by
  simp only [natOpTyPinnedF, natOpTyPinned, natOpCodF_eq] <;> rfl

theorem natOpStoredOkF_eq (env : Env) (n : Name) :
    natOpStoredOkF (mkFEnv env) n = natOpStoredOk env n := by
  simp only [natOpStoredOkF, natOpStoredOk, mkFEnv_find?,
    natOpTyPinnedF_eq] <;> rfl

theorem stdAxiomOkF_eq (env : Env) (cvA : ConstantVal) :
    stdAxiomOkF (mkFEnv env) cvA = stdAxiomOk env cvA := by
  simp only [stdAxiomOkF, stdAxiomOk, mkFEnv_find?] <;> rfl

theorem trustCompilerOkF_eq (env : Env) (cvA : ConstantVal) :
    trustCompilerOkF (mkFEnv env) cvA = trustCompilerOk env cvA := by
  simp only [trustCompilerOkF, trustCompilerOk, mkFEnv_find?] <;> rfl

theorem reduceStoredOkF_eq (env : Env) (c : Name) :
    reduceStoredOkF (mkFEnv env) c = reduceStoredOk env c := by
  simp only [reduceStoredOkF, reduceStoredOk, mkFEnv_find?] <;> rfl

theorem reduceElemOkF_eq (env : Env) (c : Name) :
    reduceElemOkF (mkFEnv env) c = reduceElemOk env c := by
  simp only [reduceElemOkF, reduceElemOk, mkFEnv_find?] <;> rfl

theorem ofReduceAxOkF_eq (env : Env) (cvA : ConstantVal) :
    ofReduceAxOkF (mkFEnv env) cvA = ofReduceAxOk env cvA := by
  simp only [ofReduceAxOkF, ofReduceAxOk, mkFEnv_find?,
    reduceElemOkF_eq, reduceStoredOkF_eq] <;> rfl

theorem reducePinGuardF_eq (env : Env) (c : Name) :
    reducePinGuardF (mkFEnv env) c = reducePinGuard env c := by
  simp only [reducePinGuardF, reducePinGuard, constsResolveF_eq] <;> rfl

theorem natOpStoredOkF_eq_fun (env : Env) :
    natOpStoredOkF (mkFEnv env) = natOpStoredOk env :=
  funext (natOpStoredOkF_eq env)

theorem divModEnvGuardF_eq (env : Env) (c : Name) :
    divModEnvGuardF (mkFEnv env) c = divModEnvGuard env c := by
  simp only [divModEnvGuardF, divModEnvGuard, mkFEnv_find?,
    natOpGuardF_eq, natOpStoredOkF_eq_fun] <;> rfl

theorem divModCertGuardF_eq (env : Env) (c : Name) (annVal : Expr)
    (hyps : List Expr) (eqE proof : Expr) :
    divModCertGuardF (mkFEnv env) c annVal hyps eqE proof
      = divModCertGuard env c annVal hyps eqE proof := by
  simp only [divModCertGuardF, divModCertGuard, constsResolveF_eq] <;> rfl

theorem divModPinGuardF_eq (ps : NatOpPinSet) (env : Env) (c : Name) :
    divModPinGuardF ps (mkFEnv env) c = divModPinGuard ps env c := by
  simp only [divModPinGuardF, divModPinGuard, constsResolveF_eq] <;> rfl

theorem divModCertsGuardF_eq (ps : NatOpPinSet) (env : Env) (c : Name)
    (annVal : Expr) :
    divModCertsGuardF ps (mkFEnv env) c annVal
      = divModCertsGuard ps env c annVal := by
  simp only [divModCertsGuardF, divModCertsGuard, divModCertGuardF_eq] <;> rfl

theorem checkEtaThmF_eq (env : Env) (T ctorName : Name)
    (lps : List Name) (nP nF : Nat) :
    checkEtaThmF mode (mkFEnv env) T ctorName lps nP nF
      = checkEtaThm mode env T ctorName lps nP nF := by
  simp only [checkEtaThmF, checkEtaThm, mkFEnv_find?] <;> rfl

theorem checkUnitThmF_eq (env : Env) (T : Name) (lps : List Name)
    (nP : Nat) :
    checkUnitThmF mode (mkFEnv env) T lps nP = checkUnitThm mode env T lps nP := by
  simp only [checkUnitThmF, checkUnitThm, mkFEnv_find?] <;> rfl

theorem indBlockCapsF_eq (env : Env) (cvT cvC : ConstantVal)
    (nP nF : Nat) :
    indBlockCapsF mode (mkFEnv env) cvT cvC nP nF
      = indBlockCaps mode env cvT cvC nP nF := by
  simp only [indBlockCapsF, indBlockCaps, checkEtaThmF_eq,
    checkUnitThmF_eq] <;> rfl

theorem ctorResidualOkF_eq (env : Env) (T ctorName : Name)
    (lps : List Name) (nP nF : Nat) (eta : Bool) :
    ctorResidualOkF mode (mkFEnv env) T ctorName lps nP nF eta
      = ctorResidualOk mode env T ctorName lps nP nF eta := by
  simp only [ctorResidualOkF, ctorResidualOk, mkFEnv_find?] <;> rfl

theorem nestedRuleShapeF_eq (env' envS : Env) (cvName : Name)
    (lps : List Name) (tyA : Expr) (mI rP cnP j : Nat) :
    nestedRuleShapeF (mkFEnv env') (mkFEnv envS) cvName lps tyA
        mI rP cnP j
      = nestedRuleShape env' envS cvName lps tyA mI rP cnP j := by
  simp only [nestedRuleShapeF, nestedRuleShape, mkFEnv_findCV?,
    constsResolveF_eq] <;> rfl

/-! ## Monadic mirrors (non-extending: plain program equalities) -/

section Monadic

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

theorem checkConstantValF_eq (ops : CheckerOps m) (env : Env)
    (cv : ConstantVal) :
    checkConstantValF ops (mkFEnv env) cv = checkConstantVal ops env cv := by
  simp only [checkConstantValF, checkConstantVal, mkFEnv_find?,
    constsResolveF_eq] <;> rfl

theorem checkMemberValF_eq (ops : CheckerOps m) (blockNames : List Name)
    (env : Env) (cv : ConstantVal) :
    checkMemberValF ops blockNames (mkFEnv env) cv
      = checkMemberVal ops blockNames env cv := by
  simp only [checkMemberValF, checkMemberVal, mkFEnv_find?,
    checkConstantValF_eq] <;> rfl

theorem checkIotaThmF_eq (ops : CheckerOps m) (env' envS : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP j : Nat) (r : RecRule) (cvj : ConstantVal)
    (cnP cnF : Nat) (rhsA : Expr) :
    checkIotaThmF mode ops (mkFEnv env') (mkFEnv envS) f cvName lps tyA
        mI rP j r cvj cnP cnF rhsA
      = checkIotaThm mode ops env' envS f cvName lps tyA
        mI rP j r cvj cnP cnF rhsA := by
  simp only [checkIotaThmF, checkIotaThm, mkFEnv_findCV?] <;> rfl

theorem checkIotaThmNF_eq (ops : CheckerOps m) (env' envS : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP j : Nat) (r : RecRule) (cvj : ConstantVal)
    (cnP cnF : Nat) (rhsA : Expr) :
    checkIotaThmNF mode ops (mkFEnv env') (mkFEnv envS) f cvName lps tyA
        mI rP j r cvj cnP cnF rhsA
      = checkIotaThmN mode ops env' envS f cvName lps tyA
        mI rP j r cvj cnP cnF rhsA := by
  simp only [checkIotaThmNF, checkIotaThmN, mkFEnv_findCV?,
    nestedRuleShapeF_eq] <;> rfl

theorem checkIotaRuleF_eq (ops : CheckerOps m) (env' envS : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP j : Nat) (r : RecRule) :
    checkIotaRuleF mode ops (mkFEnv env') (mkFEnv envS) f cvName lps tyA
        mI rP j r
      = checkIotaRule mode ops env' envS f cvName lps tyA mI rP j r := by
  simp only [checkIotaRuleF, checkIotaRule, mkFEnv_find?, mkFEnv_find?_fun,
    constsResolveF_eq, checkIotaThmF_eq, checkIotaThmNF_eq] <;> rfl

theorem checkIotaRulesF_eq (ops : CheckerOps m) (env' envS : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP : Nat) :
    ∀ (j : Nat) (rs : List RecRule),
      checkIotaRulesF mode ops (mkFEnv env') (mkFEnv envS) f cvName lps tyA
          mI rP j rs
        = checkIotaRules mode ops env' envS f cvName lps tyA mI rP j rs
  | _, [] => rfl
  | j, r :: rest => by
    simp only [checkIotaRulesF, checkIotaRules, checkIotaRuleF_eq,
      checkIotaRulesF_eq ops env' envS f cvName lps tyA mI rP
        (j + 1) rest]

theorem checkProjLookupsF_eq (env : Env) (T ctorName : Name)
    (lps : List Name) (nP nF i : Nat) :
    (checkProjLookupsF (mkFEnv env) T ctorName lps nP nF i : m _)
      = checkProjLookups env T ctorName lps nP nF i := by
  simp only [checkProjLookupsF, checkProjLookups, mkFEnv_find?] <;> rfl

theorem checkProjTyF_eq (env : Env) (T ctorName : Name)
    (lps : List Name) (mty : Expr) (nP nF : Nat) :
    (checkProjTyF (mkFEnv env) T ctorName lps mty nP nF : m _)
      = checkProjTy env T ctorName lps mty nP nF := by
  simp only [checkProjTyF, checkProjTy, constsResolveF_eq] <;> rfl

theorem checkProjRuleF_eq (ops : CheckerOps m) (env : Env) (pty : Expr)
    (cvj : ConstantVal) (lps : List Name) (nP nF i : Nat) :
    checkProjRuleF ops (mkFEnv env) pty cvj lps nP nF i
      = checkProjRule ops env pty cvj lps nP nF i := by
  simp only [checkProjRuleF, checkProjRule, constsResolveF_eq,
    domsMatchAuxA_eq, openPisAtFvarsF_eq, instPisAtF_eq,
    instLamsAtF_eq] <;> rfl

theorem checkProjIotaF_eq (ops : CheckerOps m) (env : Env)
    (T ctorName : Name)
    (lps : List Name) (cvj : ConstantVal) (nP nF i : Nat) :
    checkProjIotaF mode ops (mkFEnv env) T ctorName lps cvj nP nF i
      = checkProjIota mode ops env env T ctorName lps cvj nP nF i := by
  simp only [checkProjIotaF, checkProjIota, mkFEnv_find?, mkFEnv_env]
    <;> rfl

/-! ### The direct simple-structure path (task #82) -/

theorem checkStructDomsAtF_eq (ops : CheckerOps m) (env : Env)
    (off : Nat) (fvs doms : List Expr) :
    ∀ (j : Nat),
      checkStructDomsAtF ops (mkFEnv env) off fvs doms j
        = checkStructDomsAt ops env off fvs doms j
  | 0 => rfl
  | j + 1 => by
    simp only [checkStructDomsAtF, checkStructDomsAt, mkFEnv_env,
      checkStructDomsAtF_eq ops env off fvs doms j]

/-! ### The direct sum path (task #175 sum-types, indexed) -/

/-- `checkStructFieldSortsIF` (task #175 indexed) at `mkFEnv`. -/
theorem checkStructFieldSortsIF_eq (ops : CheckerOps m) (env : Env)
    (isProp large : Bool) (s : Level) (nP : Nat) (fvs idxArgs : List Expr) :
    ∀ (j : Nat),
      checkStructFieldSortsIF ops (mkFEnv env) isProp large s nP fvs idxArgs j
        = checkStructFieldSortsI ops env isProp large s nP fvs idxArgs j
  | 0 => rfl
  | j + 1 => by
    simp only [checkStructFieldSortsIF, checkStructFieldSortsI, mkFEnv_env,
      checkStructFieldSortsIF_eq ops env isProp large s nP fvs idxArgs j]

/-- `checkStructFieldSortsIFA` (task #175 indexed) at `List.toArray`. -/
theorem checkStructFieldSortsIFA_eq (ops : CheckerOps m) (fe : FEnv)
    (isProp large : Bool) (s : Level) (nP : Nat) (fvs idxArgs : List Expr) :
    ∀ j, checkStructFieldSortsIFA ops fe isProp large s nP fvs.toArray idxArgs j
      = checkStructFieldSortsIF ops fe isProp large s nP fvs idxArgs j
  | 0 => rfl
  | j + 1 => by
    simp only [checkStructFieldSortsIFA, checkStructFieldSortsIF,
      List.getElem?_toArray,
      checkStructFieldSortsIFA_eq ops fe isProp large s nP fvs idxArgs j]

theorem normCtorValF_eq (ops : CheckerOps m) (env : Env) (T : Name) (nP nF : Nat)
    (cvC cvCa : ConstantVal) :
    normCtorValF ops (mkFEnv env) T nP nF cvC cvCa = normCtorVal ops env T nP nF cvC cvCa := by
  simp only [normCtorValF, normCtorVal, mkFEnv_env, checkConstantValF_eq]

theorem checkSumCtorF_eq (ops : CheckerOps m) (env₀ env : Env) (T : Name)
    (lps : List Name) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (cvC : ConstantVal) (nF : Nat) (cvTa : ConstantVal) :
    checkSumCtorF ops (mkFEnv env₀) (mkFEnv env) T lps nP nIdx resSort isProp
        large cvC nF cvTa
      = checkSumCtor ops env₀ env T lps nP nIdx resSort isProp large cvC nF
        cvTa := by
  simp only [checkSumCtorF, checkSumCtor, checkConstantValF_eq, normCtorValF_eq,
    checkStructDomsAtFA_eq, checkStructDomsAtF_eq, openPisAtFvarsF_eq,
    checkStructFieldSortsIFA_eq, checkStructFieldSortsIF_eq, constsResolveF_eq]

theorem checkSumCtorsF_eq (ops : CheckerOps m) (env₀ env : Env) (T : Name)
    (lps : List Name) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (cvTa : ConstantVal) :
    ∀ (cs : List (ConstantVal × Nat)),
      checkSumCtorsF ops (mkFEnv env₀) (mkFEnv env) T lps nP nIdx resSort isProp
          large cvTa cs
        = checkSumCtors ops env₀ env T lps nP nIdx resSort isProp large cvTa cs
  | [] => rfl
  | c :: cs => by
    simp only [checkSumCtorsF, checkSumCtors, checkSumCtorF_eq,
      checkSumCtorsF_eq ops env₀ env T lps nP nIdx resSort isProp large cvTa cs]

omit [MonadExceptOf CheckError m] in
theorem checkDivModCertsF_eq (ops : CheckerOps m) (env : Env) (c : Name)
    (annVal : Expr) :
    ∀ (stmts : List (List Expr × Expr)) (proofs : List Expr),
      checkDivModCertsF ops (mkFEnv env) c annVal stmts proofs
        = checkDivModCerts ops env c annVal stmts proofs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | (_, _) :: _, [] => rfl
  | (hyps, eqE) :: srest, proof :: prest => by
    simp only [checkDivModCertsF, checkDivModCerts, divModCertGuardF_eq,
      mkFEnv_env, checkDivModCertsF_eq ops env c annVal srest prest]

omit [MonadExceptOf CheckError m] in
theorem checkDivModPinAtF_eq (ops : CheckerOps m) (env : Env) (c : Name)
    (value' : Expr) (ps : NatOpPinSet) :
    checkDivModPinAtF ops (mkFEnv env) c value' ps
      = checkDivModPinAt ops env c value' ps := by
  simp only [checkDivModPinAtF, checkDivModPinAt, mkFEnv_env,
    checkDivModCertsF_eq]

theorem checkDivModPinLoopF_eq (ops : CheckerOps m) (env : Env) (c : Name)
    (value' : Expr) :
    ∀ (pss : List NatOpPinSet) (tried : List String),
      checkDivModPinLoopF ops (mkFEnv env) c value' pss tried
        = checkDivModPinLoop ops env c value' pss tried
  | [], _ => rfl
  | ps :: rest, tried => by
    simp only [checkDivModPinLoopF, checkDivModPinLoop, divModPinGuardF_eq,
      divModCertsGuardF_eq, checkDivModPinAtF_eq,
      checkDivModPinLoopF_eq ops env c value' rest]

theorem checkDivModPinF_eq (ops : CheckerOps m) (env env2 : Env)
    (c : Name) :
    checkDivModPinF ops pins (mkFEnv env) (mkFEnv env2) c
      = checkDivModPin ops pins env env2 c := by
  simp only [checkDivModPinF, checkDivModPin, mkFEnv_find?,
    divModEnvGuardF_eq, checkDivModPinLoopF_eq] <;> rfl

theorem checkReducePinF_eq (ops : CheckerOps m) (env env2 : Env)
    (c : Name) (value : Expr) :
    checkReducePinF ops (mkFEnv env) (mkFEnv env2) c value
      = checkReducePin ops env env2 c value := by
  simp only [checkReducePinF, checkReducePin, mkFEnv_env,
    reduceStoredOkF_eq, reduceElemOkF_eq, reducePinGuardF_eq] <;> rfl

end Monadic

/-! ## Environment-extending mirrors: the push equation

Each extending mirror is its generic counterpart followed by `mkFEnv`
— the pushed index of the cons-extended environment *is* `mkFEnv` of
it.  The monadic `_push` equations that consume it are stated at the
executing monad, in `ConLeche/Verify/Cached/BridgeCSDecl.lean`; the
`CheckIM` copies here went with the interned drivers (task #172). -/

theorem push_mkFEnv (env : Env) (ci : ConstantInfo) :
    (mkFEnv env).push ci = mkFEnv ⟨ci :: env.consts⟩ := rfl

/-- The direct sum's constructor conses through the index (task #175
sum-types): the pushed index of the consed environment *is* `mkFEnv`
of it. -/
theorem consSumCtorsF_mkFEnv (nP : Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (env : Env),
      consSumCtorsF nP cs (mkFEnv env) = mkFEnv (consSumCtors nP cs env)
  | [], _ => rfl
  | c :: cs, env => by
    simp only [consSumCtorsF, consSumCtors, push_mkFEnv,
      consSumCtorsF_mkFEnv nP cs ⟨.ctorInfo c.1 nP c.2 :: env.consts⟩]

/-! ## The direct recursive install's mirrors (task #188) -/

section FixMirrors

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

theorem nativeOpenedOkF_eq (env₀ : Env) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (cty : Expr) (nF : Nat) (ks : List RecFieldKind) :
    nativeOpenedOkF .plain (mkFEnv env₀) T lps nP nIdx cty nF ks
      = nativeOpenedOk env₀ T lps nP nIdx cty nF ks := by
  simp only [nativeOpenedOkF, nativeOpenedOk, StructWalkers.plain, constsResolveF_eq]
    <;> rfl

theorem nativeFieldsOkF_eq (env₀ : Env) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (ctorsA : List (ConstantVal × Nat)) (kinds : List (List RecFieldKind)) :
    nativeFieldsOkF .plain (mkFEnv env₀) T lps nP nIdx ctorsA kinds
      = nativeFieldsOk env₀ T lps nP nIdx ctorsA kinds := by
  simp only [nativeFieldsOkF, nativeFieldsOk, nativeOpenedOkF_eq] <;> rfl

theorem checkNativeRulesF_eq (envR : Env) (rlps : List Name) (T : Name) (lps : List Name)
    (elim : Name) (large : Bool) (nP nIdx : Nat) (tty : Expr)
    (ctors : List (Name × Nat × Expr × List Nat)) (recC : Name) (rlvls : List Level) :
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

theorem checkNativeRecF_eq (ops : CheckerOps m) (env : Env) (p : NativeParts)
    (cvTa : ConstantVal) (ctorsA : List (ConstantVal × Nat)) :
    checkNativeRecF ops .plain (mkFEnv env) p cvTa ctorsA
      = checkNativeRec ops env p cvTa ctorsA := by
  simp only [checkNativeRecF, checkNativeRec, mkFEnv_env, checkConstantValF_eq,
    push_mkFEnv, checkNativeRulesF_eq]
  simp only [StructWalkers.plain, constsResolveF_eq]

end FixMirrors

end ConLeche
