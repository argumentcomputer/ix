module

public import ConLeche.Kernel.Inductives.SumInstallF
import ConLeche.Kernel.Inductives.NativeInstall

@[expose] public section

/-!
# The direct recursive install, through the index (task #188)

`checkNative`'s recursor stage (`ConLeche/Kernel/Inductives/NativeInstall.lean`)
over an `FEnv`, the mirror the cached drivers run; the former's and
the constructors' stages are the sum route's mirrors.
-/

namespace ConLeche

section Mirrors

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- `nativeOpenedOk` through the index. -/
def nativeOpenedOkF (w : StructWalkers) (fe₀ : FEnv) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (cty : Expr) (nF : Nat) (ks : List RecFieldKind) : Bool :=
  match openPisAtFvars nP cty 0 with
  | some (fvsP, crest) =>
    match openPisAtFvars nF crest nP with
    | some (xFvs, xrest) =>
      (xrest.getAppArgs.drop nP).all (w.resolve fe₀) &&
      (List.range nF).all fun i =>
        match xFvs[i]?, ks.getD i .ordinary with
        | some x, .ordinary => w.resolve fe₀ x.fvarTypeD
        | some x, .recursive =>
          x.fvarTypeD.getAppFn == Expr.const T (lps.map .param) &&
          x.fvarTypeD.getAppArgs.take nP == fvsP &&
          x.fvarTypeD.getAppArgs.length == nP + nIdx &&
          (x.fvarTypeD.getAppArgs.drop nP).all (w.resolve fe₀) &&
          !(xFvs.drop (i + 1)).any (fun y => y.fvarTypeD.mentionsFvar (nP + i)) &&
          !xrest.mentionsFvar (nP + i)
        | some x, .reflexive =>
          -- the field's own telescope, OPENED at variables at the field's
          -- depth (as the constructor's was): its domains resolve in
          -- `env₀` (so they are free of the block), its body is the family
          -- at the parameter variables and `nIdx` index expressions
          -- resolving in `env₀` (task #202)
          match openPisAtFvars (x.fvarTypeD.piBinders).1.length x.fvarTypeD (nP + i) with
          | some (afvs, body) =>
            afvs.length != 0 &&
            afvs.all (fun a => w.resolve fe₀ a.fvarTypeD) &&
            body.getAppFn == Expr.const T (lps.map .param) &&
            body.getAppArgs.take nP == fvsP &&
            body.getAppArgs.length == nP + nIdx &&
            (body.getAppArgs.drop nP).all (w.resolve fe₀) &&
            !(xFvs.drop (i + 1)).any (fun y => y.fvarTypeD.mentionsFvar (nP + i)) &&
            !xrest.mentionsFvar (nP + i)
          | none => false
        | _, _ => false
    | none => false
  | none => false

/-- `nativeFieldsOk` through the index. -/
def nativeFieldsOkF (w : StructWalkers) (fe₀ : FEnv) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (ctorsA : List (ConstantVal × Nat)) (kinds : List (List RecFieldKind)) : Bool :=
  ctorsA.length == kinds.length &&
  (List.range ctorsA.length).all fun j =>
    match ctorsA[j]?, kinds[j]? with
    | some cA, some ks =>
      ks.length == cA.2 && nativeOpenedOkF w fe₀ T lps nP nIdx cA.1.type cA.2 ks
    | _, _ => false

/-- `checkNativeRules` through the index. -/
def checkNativeRulesF (w : StructWalkers) (feR : FEnv) (rlps : List Name) (T : Name) (lps : List Name)
    (elim : Name) (large : Bool) (nP nIdx : Nat) (tty : Expr)
    (ctors : List (Name × Nat × Expr × List Nat)) (recC : Name) (rlvls : List Level) :
    Nat → Nat → m (List Expr)
  | 0, _ => pure []
  | k + 1, j => do
    let rhs ← unwrapOr (structRecRhsR T lps elim large nP nIdx tty ctors recC rlvls j)
      (.internal "direct rec: recursor rule")
    unless rhs.allLevelParamsDefined rlps && w.resolve feR rhs &&
        rhs.looseBVarsBounded 0 && !rhs.hasFvar do
      throw (.internal "direct rec: recursor rule scoping")
    let rest ← checkNativeRulesF w feR rlps T lps elim large nP nIdx tty ctors recC rlvls k
      (j + 1)
    pure (rhs :: rest)

/-- `checkNativeRec` through the index. -/
def checkNativeRecF (ops : CheckerOps m) (w : StructWalkers) (fe : FEnv) (p : NativeParts)
    (cvTa : ConstantVal) (ctorsA : List (ConstantVal × Nat)) :
    m (ConstantVal × List Expr) := do
  -- the recursor pin (task #220), as in `checkNativeRec`
  unless p.cvR.name == p.cvT.name.str "rec" do
    throw (.invalid "direct rec: the block's recursor is not the generated T.rec")
  unless nativeRecLpsOk p.toInductiveShape do
    throw (.invalid "direct rec: the recursor's level parameters are not the generated ones")
  unless p.recPinned do
    throw (.invalid "direct rec: the recursor record is not the generated recursor")
  let cvRi ← checkConstantValF ops fe p.cvR
  let T := p.cvT.name
  let lps := p.cvT.levelParams
  let ctors := nativeCtors4 ctorsA p.kinds
  let recTy ← unwrapOr (structRecTyR T lps p.elim p.large p.nP p.nIdx cvTa.type ctors)
    (.internal "direct rec: recursor type")
  unless recTy.allLevelParamsDefined p.cvR.levelParams && w.resolve fe recTy &&
      recTy.looseBVarsBounded 0 && !recTy.hasFvar do
    throw (.internal "direct rec: recursor type scoping")
  let sty ← ops.inferType fe.env 0 recTy
  let _u ← ops.ensureSort fe.env 0 sty
  unless ← ops.isDefEq fe.env 0 cvRi.type recTy do
    throw (.invalid "direct rec: recursor type is not the generated one")
  let cvRa : ConstantVal := ⟨p.cvR.name, p.cvR.levelParams, recTy⟩
  let feR := fe.push (.recInfo cvRa p.majorIdx p.rulePrefix [])
  let rhss ← checkNativeRulesF w feR p.cvR.levelParams T lps p.elim p.large p.nP p.nIdx
    cvTa.type ctors p.cvR.name (p.cvR.levelParams.map .param) ctors.length 0
  pure (cvRa, rhss)

/-- `checkNativeTable` through the index (task #210 Part A). -/
def checkNativeTableF (w : StructWalkers) (p : NativeParts) (ctorsA : List (ConstantVal × Nat))
    (sortss : List (List Level)) (fe : FEnv) : m FEnv :=
  match ctorsA, sortss with
  | [cA], [sorts] =>
    if p.nIdx == 0 then
      checkStructProjTableF w p.cvT.name cA.1.name p.cvT.levelParams p.nP cA.2 p.resSort
        (structProjGuards cA.1.type p.nP cA.2 sorts) 1 cA.1 fe
    else pure fe
  | _, _ => pure fe

end Mirrors

end ConLeche
