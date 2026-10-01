module

public import ConLeche.Kernel.Inductives.StructInstallF

@[expose] public section

/-!
# The direct sum install, through the index

`checkSum`'s stages (`ConLeche/Kernel/Inductives/SumInstall.lean`)
over an `FEnv`, the mirrors the cached drivers run.
-/

namespace ConLeche

section Mirrors

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- `checkSumTele` through the index (task #195): the whnf loop
runs at the index's environment through the shared operations, the
re-check of the closed telescope is `checkConstantValF`. -/
def checkSumTeleF (ops : CheckerOps m) (fe : FEnv) (cv : ConstantVal) (n : Nat)
    (cvTa₀ : ConstantVal) : m (ConstantVal × Level) :=
  match cvTa₀.type.stripPis n with
  | some (_, .sort s) => pure (cvTa₀, s)
  | _ => do
    let (bs, s) ← whnfTelescope ops fe.env 0 n cvTa₀.type
    let cvTa ← checkConstantValF ops fe { cv with type := closeTelescope bs 0 (.sort s) }
    pure (cvTa, s)

/-- `checkSumInd` through the index. -/
def checkSumIndF (ops : CheckerOps m) (fe : FEnv) (p : InductiveShape)
    (capsOf : InductiveShape → IndCaps) :
    m (FEnv × ConstantVal × InductiveShape) := do
  let cvTa₀ ← checkConstantValF ops fe p.cvT
  let (cvTa, s) ← checkSumTeleF ops fe p.cvT (p.nP + p.nIdx) cvTa₀
  let (_, tbody) ← unwrapOr (cvTa.type.stripPis (p.nP + p.nIdx))
    (.internal "direct sum: type former telescope")
  unless tbody == Expr.sort s do
    throw (.internal "direct sum: type former result sort")
  let p' := p.withSort s
  pure (fe.push (.indInfo cvTa (capsOf p')), cvTa, p')

/-- `checkStructFieldSortsI` through the index. -/
def checkStructFieldSortsIF (ops : CheckerOps m) (fe : FEnv) (isProp large : Bool)
    (s : Level) (nP : Nat) (fvs idxArgs : List Expr) : Nat → m (List Level)
  | 0 => pure []
  | j + 1 => do
    let fv ← unwrapOr fvs[j]? (.internal "direct sum: field index")
    let ty ← ops.inferType fe.env (nP + j) fv.fvarTypeD
    let u ← ops.ensureSort fe.env (nP + j) ty
    if !isProp then
      unless ← liftFueled "level comparison" (Level.leq u s) do
        throw (.invalid "direct sum: field universe too large")
    else if large then
      unless Level.isEquiv u .zero == some true || idxArgs.contains fv do
        throw (.invalid "direct sum: large eliminator with a non-propositional \
          field outside the indices")
    let rest ← checkStructFieldSortsIF ops fe isProp large s nP fvs idxArgs j
    pure (rest ++ [u])

/-- `checkStructFieldSortsIF` over an array of field variables (the
callers convert once).  Equal to it at `List.toArray`:
`checkStructFieldSortsIFA_eq`. -/
def checkStructFieldSortsIFA (ops : CheckerOps m) (fe : FEnv) (isProp large : Bool)
    (s : Level) (nP : Nat) (fvs : Array Expr) (idxArgs : List Expr) : Nat → m (List Level)
  | 0 => pure []
  | j + 1 => do
    let fv ← unwrapOr fvs[j]? (.internal "direct sum: field index")
    let ty ← ops.inferType fe.env (nP + j) fv.fvarTypeD
    let u ← ops.ensureSort fe.env (nP + j) ty
    if !isProp then
      unless ← liftFueled "level comparison" (Level.leq u s) do
        throw (.invalid "direct sum: field universe too large")
    else if large then
      unless Level.isEquiv u .zero == some true || idxArgs.contains fv do
        throw (.invalid "direct sum: large eliminator with a non-propositional \
          field outside the indices")
    let rest ← checkStructFieldSortsIFA ops fe isProp large s nP fvs idxArgs j
    pure (rest ++ [u])

/-- `normCtorVal` through the index (the whnf walk at `fe.env`, the
re-check through `checkConstantValF`). -/
def normCtorValF (ops : CheckerOps m) (fe : FEnv) (T : Name) (nP nF : Nat)
    (cvC cvCa : ConstantVal) : m ConstantVal := do
  let (cbs, _) ← unwrapOr (cvCa.type.stripPis nP)
    (.notImplemented "direct sum: constructor telescope")
  let (fvsP, crest) ← unwrapOr (openPisAtFvars nP cvCa.type 0)
    (.notImplemented "direct sum: constructor telescope")
  let pbs := List.zipWith (fun (x : Expr) (b : Expr × BinderMeta) => (x.fvarTypeD, b.2)) fvsP cbs
  let (fbs, resid) ← normFieldDoms ops fe.env T nP nF crest
  let ty' := closeTelescope (pbs ++ fbs) 0 resid
  if ty' == cvCa.type then pure cvCa
  else checkConstantValF ops fe { cvC with type := ty' }

/-- `checkSumCtor` through the index. -/
def checkSumCtorF (ops : CheckerOps m) (fe₀ fe : FEnv) (T : Name)
    (lps : List Name) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (cvC : ConstantVal) (nF : Nat) (cvTa : ConstantVal) : m (ConstantVal × List Level) := do
  let cvCa₀ ← checkConstantValF ops fe cvC
  let cvCa ← normCtorValF ops fe T nP nF cvC cvCa₀
  let (_, cbody) ← unwrapOr (cvCa.type.stripPis (nP + nF))
    (.notImplemented "direct sum: constructor telescope")
  -- official's `is_valid_ind_app` on the constructor's result
  -- ("invalid return type for 'C'", `check_constructors`): a REJECT,
  -- not a decline (task #220) — the head must be the block at its own
  -- level parameters, applied to exactly the parameters and `nIdx`
  -- further arguments
  unless structCtorResidOk T lps nP nF nIdx cbody do
    throw (.invalid "direct sum: invalid constructor return type")
  let cq ← unwrapOr (openPisAtFvarsF nP cvCa.type 0)
    (.notImplemented "direct sum: constructor telescope")
  let tq ← unwrapOr (openPisAtFvarsF nP cvTa.type 0)
    (.notImplemented "direct sum: type former telescope")
  checkStructDomsAtFA ops fe 0 cq.1.toArray (tq.1.map Expr.fvarTypeD).toArray nP
  let xq ← unwrapOr (openPisAtFvarsF nF cq.2 nP)
    (.notImplemented "direct sum: constructor field telescope")
  unless xq.2.getAppFn == Expr.const T (lps.map .param) &&
      xq.2.getAppArgs.take nP == cq.1 && xq.2.getAppArgs.length == nP + nIdx do
    throw (.notImplemented "direct sum: opened constructor residual")
  unless xq.1.all fun x => x.fvarTypeD.constsResolveF fe₀ do
    throw (.notImplemented "direct sum: field domain after the block")
  unless (xq.2.getAppArgs.drop nP).all fun e => e.constsResolveF fe₀ do
    throw (.invalid "direct sum: index expression mentions the block")
  let sorts ← checkStructFieldSortsIFA ops fe isProp large resSort nP xq.1.toArray
    (xq.2.getAppArgs.drop nP) nF
  pure (cvCa, sorts)

/-- `checkSumCtors` through the index. -/
def checkSumCtorsF (ops : CheckerOps m) (fe₀ fe : FEnv) (T : Name)
    (lps : List Name) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (cvTa : ConstantVal) :
    List (ConstantVal × Nat) → m (List (ConstantVal × Nat) × List (List Level))
  | [] => pure ([], [])
  | c :: cs => do
    let (cvCa, sorts) ← checkSumCtorF ops fe₀ fe T lps nP nIdx resSort isProp large c.1 c.2
      cvTa
    let (rest, srest) ← checkSumCtorsF ops fe₀ fe T lps nP nIdx resSort isProp large cvTa cs
    pure ((cvCa, c.2) :: rest, sorts :: srest)

/-- `consSumCtors` through the index. -/
def consSumCtorsF (nP : Nat) : List (ConstantVal × Nat) → FEnv → FEnv
  | [], fe => fe
  | c :: cs, fe => consSumCtorsF nP cs (fe.push (.ctorInfo c.1 nP c.2))

end Mirrors

end ConLeche
