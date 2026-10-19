/-
  Ix.AuxGen.AuxKernel: the kernel interface AuxGen's generators ask
  (AuxGen M0, CQ2.16).

  The generators (`Recursor`, `Below`, `BRecOn`, `Patches`, `CompileAux`)
  need a kernel for a handful of questions: the sort level of a type, the
  weak head normal form of a term, definitional equality, the type of a term
  (for a decision), the block's elimination decision, and an environment
  that holds the constants those questions name. This module states those
  questions as an interface over a closed sum of backends. M0 has one
  backend, `Ix.Tc` through the bridge (`Ix.AuxGen.Kernel`), constructed at
  `compileMutualAuxTail`'s caller and the decompile driver's `runK`. AuxGen
  M2a adds IxC's Source mode beside it for `.below`'s scopes (the `ixc` arm,
  in the modes `shadow`, `fallback`, `failClosed`; below), which only the
  measurement fold constructs.

  ## The contract

  1. **Inputs.** Constants are referenced by Lean names. Terms are open
     `Ix.Expr`: free variables are the scope's `LocalDecl.fvarName`s, level
     parameters are the scope's names, and bound variables appear only
     under binders inside the term. Anything else is refused
     (`AuxKernelError`); nothing is invented — no `Sort 0`, no
     `_dangling_fvar_N`, no `u_{idx}`, no `panic!`.
  2. **Scopes are values.** `AuxScope.new` refuses duplicate level
     parameters and duplicate outer variables; `push` refuses an identity
     already in scope; `pop` removes exactly the most recently pushed
     telescope, never outer locals. An answer depends only on the scope
     argument's `(levelParams, locals)` and the kernel's environment. A
     backend that cannot serve a scope value refuses it (`staleScope`):
     `Ix.Tc` serves the values whose kernel context is live (every linearly
     threaded value); IxC (M1) serves all of them. `push` may check
     domains (IxC annotates them, `Ix.Tc`'s infer-only scope does not);
     generators must not rely on either.
  3. **`getLevel`** spells levels as Lean's elaborator does: the
     `inferAppType` fast path when the head's declared type in the KERNEL's
     environment telescopes to a `Sort` (canonical `.below` types after
     `admitGenerated`, not the Lean environment); otherwise infer, then
     `ensureSort`; ∀-typed results are `levelNormalize`d. It fails closed
     (`AuxKernelError.kernel`).
  4. **`whnf?`** is the weak head normal form with source spellings
     restored: with the same content it keeps the input's names and the
     result's binder infos and levels; after a real reduction, BVar-free
     `App`/`Proj` subterms matching an input subterm take the input's
     spelling. `none` means the kernel gave no answer; generators default to
     the input (`whnfOrInput`).
  5. **`isDefEq?`** is the kernel's definitional equality in the scope;
     `none` means no answer; generators default to `false`
     (`isDefEqOrFalse`), which can switch Eq to HEq.
  6. **`inferType?`** is for decisions only: its result is never emitted
     into generated terms and gets no restoration. `none` means no answer.
  7. **Results out.** A result that does not denote a term over the scope
     is refused (the egress constructors of `AuxKernelError`).
  8. **`elimDecision`** is Lean's `elim_only_at_universe_zero` over the
     expanded block (the original classes and the nested auxiliaries,
     `nFlat` members in all): the WHNF-peeled result sort; small, without
     probing a field, when that level may be zero and the expanded block is
     not a singleton; otherwise the original classes' probe. It fails
     closed with the `invalidMutualBlock` texts. It may supersede scopes,
     and does in `Ix.Tc`.
  9. **Environment hooks.** After `admitGenerated cs`, a query naming a
     constant of `cs` sees the generated declaration (`Ix.Tc` overwrites the
     kenv entry at that name's address; IxC will use a fresh key and σ).
     `Ix.Tc`'s answers depend on what has been admitted, because type stubs
     do not unfold and fault-in upgrades them: a backend property M1–M4
     measure, not a contract.
  10. **Determinism.** An answer is a function of the handle, the state and
     the arguments; it does not depend on `HashMap` iteration order.
     Running out of fuel is a kernel error.

  The `Ix.Tc` arm calls exactly the bridge functions the generators called
  before M0, with the same arguments in the same order; the scope checks
  only read state. So the switch is byte-identical, and the runtime closure
  of `Ix.Cert.compile` is unchanged (dispatch is ordinary code).

  ## The IxC arm (AuxGen M2a, a measurement mode)

  `ixc maps oracle` is `Ix.Tc` over `maps` for every generator, except the
  scopes a generator opens with `route := .below` (`.below`'s two scopes),
  which ask IxC Source mode through `oracle` (`Ix.AuxGen.Oracle`), in the
  oracle's mode (`IxcMode`):
  * `shadow`: both kernels answer every question; `Ix.Tc`'s answer is used.
  * `fallback`: both answer; IxC's answer is used where it answers.
  * `failClosed`: IxC alone; a refusal fails the block.

  The arm only calls the oracle's closures, so no production path reaches
  IxC through it (`Ix.AuxGen.Oracle`'s docstring). Under `shadow` and
  `fallback` the `Ix.Tc` scope is opened, pushed, popped and asked exactly as
  on the `Ix.Tc` arm, so `Ix.Tc`'s environment evolves as in production. Each
  question is counted in `AuxKernelCtx.ixcStats`.

  Before `.below`, the tail asks the kernel to install the block's own
  canonical flat block (`withFlatBlock`): `Ix.Tc` needs nothing; IxC
  installs it when the block's layout is not Lean's, so `.below`'s terms
  read through σ.

  An IxC-only scope (`failClosed`) answers `getLevel`; it gives no answer to
  `whnf?`, `isDefEq?` and `inferType?` (`.below` asks none of them).
-/
module
public import Ix.AuxGen.Kernel
public import Ix.AuxGen.Oracle
public section

namespace Ix.AuxGen

open Ix.CompileM (CompileM CompileError)

/-- The kernel AuxGen asks, with that kernel's environment. One value per
    AuxGen run (a compile block's tail, one decompile Pass-2 call). -/
inductive AuxKernel where
  /-- `Ix.Tc` over the bridge kenv; `maps` gives provisional addresses. -/
  | tc (maps : AddrMaps)
  /-- AuxGen M2a's measurement mode: `Ix.Tc` over `maps`, and IxC Source mode
      through `oracle` for the scopes routed to it (`AuxRoute.below`). -/
  | ixc (maps : AddrMaps) (oracle : AuxOracle)

/-- The addresses `Ix.Tc` resolves through. -/
def AuxKernel.maps : AuxKernel → AddrMaps
  | .tc maps => maps
  | .ixc maps _ => maps

/-- Which generator opens a scope (AuxGen M2a): `.below`'s scopes ask IxC on
    the `ixc` arm. -/
inductive AuxRoute where
  | tc
  | below
  deriving BEq, Inhabited

/-- How `admitSource` loads a source constant. -/
inductive AdmitMode where
  /-- The constant as it is (`ensureInKenvOf`). -/
  | full
  /-- Theorem and opaque values as type stubs (`ensureInKenvOfPrewarm`). -/
  | prewarm
  deriving BEq, Inhabited

/-- The `Ix.Tc` half of a scope value: the bridge view and the identity of
    the kernel context it denotes. -/
structure TcScopeRef where
  view : TcScopeSt
  /-- `AuxKernelCtx.scopeEpoch` when the value was made. -/
  epoch : Nat
  /-- `Ix.Tc`'s content-addressed context id after this value's last
      `new`/`push`/`pop`. -/
  ctxId : Address

/-- A scope value's backend part. -/
inductive AuxScopeBackend where
  | tc (ref : TcScopeRef)
  /-- IxC alone (`failClosed`). -/
  | ixc (scope : OracleScope)
  /-- `Ix.Tc`, and IxC beside it (`shadow`, `fallback`); `none` once IxC
      refused the scope. -/
  | both (ref : TcScopeRef) (scope : Option OracleScope)

/-- A local context as a value. It denotes `(levelParams, locals)`. -/
structure AuxScope where
  kernel : AuxKernel
  levelParams : Array Name
  /-- Outermost first: the outer context, then the pushed locals. -/
  locals : Array LocalDecl
  /-- The locals from `new`; `pop` cannot remove them. -/
  nOuter : Nat
  backend : AuxScopeBackend

/-! ## The IxC arm's bookkeeping -/

/-- Update the tail's IxC counts. -/
def bumpIxc (f : IxcStats → IxcStats) : KBridgeM Unit :=
  modify fun k => { k with ixcStats := f k.ixcStats }

/-- A telescope as the oracle takes it. -/
def oracleLocals (decls : Array LocalDecl) : Array (Name × Expr) :=
  decls.map fun d => (d.fvarName, d.domain)

/-- The oracle's mode on the `ixc` arm. -/
def AuxKernel.ixcMode? : AuxKernel → Option IxcMode
  | .ixc _ o => some o.mode
  | .tc _ => none

namespace AuxScope

/-- The scope's depth: its number of locals. -/
def depth (s : AuxScope) : Nat := s.locals.size

/-- The current `Ix.Tc` reference for `view`. -/
private def tcRef (view : TcScopeSt) : KBridgeM TcScopeRef := do
  let ctx ← get
  return { view, epoch := ctx.scopeEpoch, ctxId := ctx.tcState.ctxId }

/-- The bridge view of an `Ix.Tc` reference, if the context it denotes is
    live: no newer scope or elimination decision replaced the type checker
    (the epoch), and the type checker's context is the one the value left
    (`ctxId`, which `Ix.Tc` restores on every outcome of a query). Depth
    alone would not do: after `push [x]`, `pop`, `push [y]` the depth
    matches, but `x` would be answered as `y`. Otherwise the value is
    refused (`staleScope`). This only reads state. -/
private def tcLive (r : TcScopeRef) (op : String) : KBridgeM TcScopeSt := do
  let ctx ← get
  if r.epoch == ctx.scopeEpoch && r.ctxId == ctx.tcState.ctxId then
    return r.view
  throwBridge (.staleScope op)

/-- The bridge view of a scope value, if its backend can serve it: the
    `Ix.Tc` part's (`tcLive`). An IxC-only scope has none (`staleScope`). -/
def live? (s : AuxScope) (op : String) : KBridgeM TcScopeSt := do
  match s.backend with
  | .tc r | .both r _ => tcLive r op
  | .ixc _ => throwBridge (.staleScope op)

/-- The `Ix.Tc` scope's own checks, for an IxC-only scope: duplicate level
    parameters and outer variables are refused as `TcScopeSt.new` refuses
    them. -/
private def checkScopeNames (ctx : Array LocalDecl) (lps : Array Name) : KBridgeM Unit := do
  let mut seenParams : Std.HashSet Name := {}
  for name in lps do
    if seenParams.contains name then throwBridge (.duplicateLevelParam name)
    seenParams := seenParams.insert name
  let mut seen : Std.HashSet Name := {}
  for decl in ctx do
    if seen.contains decl.fvarName then throwBridge (.duplicateOuterFVar decl.fvarName)
    seen := seen.insert decl.fvarName

/-- IxC's scope over `ctx`, or `none` (counted) when IxC refuses it. -/
private def ixcNew (o : AuxOracle) (ctx : Array LocalDecl) (lps : Array Name) :
    KBridgeM (Option OracleScope × Option String) := do
  match o.newScope lps (oracleLocals ctx) with
  | .ok s => return (some s, none)
  | .error e =>
    bumpIxc fun st => (st.sample s!"scope new: {e}") |> fun st =>
      { st with scopesRefused := st.scopesRefused + 1 }
    return (none, some e)

/-- Open a scope over `ctx` with level parameters `lps`, for the generator
    `route`. -/
def new (k : AuxKernel) (ctx : Array LocalDecl) (lps : Array Name)
    (route : AuxRoute := .tc) : KBridgeM AuxScope := do
  match k, route with
  | .ixc maps o, .below =>
    if o.mode == .failClosed then
      checkScopeNames ctx lps
      match ← ixcNew o ctx lps with
      | (some s, _) =>
        return { kernel := k, levelParams := lps, locals := ctx, nOuter := ctx.size,
                 backend := .ixc s }
      | (none, e) => throwBridge (.kernel (.ixc "scope") (e.getD ""))
    let view ← TcScopeSt.new ctx lps maps
    let (s?, _) ← ixcNew o ctx lps
    return { kernel := k, levelParams := lps, locals := ctx, nOuter := ctx.size,
             backend := .both (← tcRef view) s? }
  | k, _ =>
    let view ← TcScopeSt.new ctx lps k.maps
    return { kernel := k, levelParams := lps, locals := ctx, nOuter := ctx.size,
             backend := .tc (← tcRef view) }

/-- IxC's half of a `push`/`pop` on a `both` scope: the scope after it, or
    `none` (counted) when IxC refuses it. -/
private def ixcStep (op : String) (s? : Option OracleScope)
    (step : OracleScope → Except String OracleScope) : KBridgeM (Option OracleScope) := do
  let some s := s? | return none
  match step s with
  | .ok s' => return some s'
  | .error e =>
    bumpIxc fun st => (st.sample s!"scope {op}: {e}") |> fun st =>
      { st with scopesRefused := st.scopesRefused + 1 }
    return none

/-- Push a telescope onto the scope. -/
def push (s : AuxScope) (decls : Array LocalDecl) : KBridgeM AuxScope := do
  match s.backend with
  | .tc r =>
    let view ← (← tcLive r "push").pushLocals decls
    return { s with locals := s.locals ++ decls, backend := .tc (← tcRef view) }
  | .ixc o =>
    for decl in decls do
      if s.locals.any (·.fvarName == decl.fvarName) then
        throwBridge (.duplicatePushedFVar decl.fvarName)
    match o.push (oracleLocals decls) with
    | .ok o' => return { s with locals := s.locals ++ decls, backend := .ixc o' }
    | .error e => throwBridge (.kernel (.ixc "push") e)
  | .both r o? =>
    let view ← (← tcLive r "push").pushLocals decls
    let o' ← ixcStep "push" o? (·.push (oracleLocals decls))
    return { s with locals := s.locals ++ decls, backend := .both (← tcRef view) o' }

/-- Pop the most recently pushed telescope `decls`. -/
def pop (s : AuxScope) (decls : Array LocalDecl) : KBridgeM AuxScope := do
  -- `popLocals` refuses a pop beyond the pushed locals or out of order, so
  -- the truncation below removes exactly `decls`.
  let keep := s.locals.size - decls.size
  match s.backend with
  | .tc r =>
    let view ← (← tcLive r "pop").popLocals decls
    return { s with locals := s.locals.extract 0 keep, backend := .tc (← tcRef view) }
  | .ixc o =>
    -- the same refusals as `popLocals`
    if decls.size > s.locals.size - s.nOuter then throwBridge .popExceedsPushed
    for (decl, i) in decls.zipIdx do
      if (s.locals[keep + i]?.map (·.fvarName == decl.fvarName)) != some true then
        throwBridge (.popNotLifo decl.fvarName)
    match o.pop decls.size with
    | .ok o' => return { s with locals := s.locals.extract 0 keep, backend := .ixc o' }
    | .error e => throwBridge (.kernel (.ixc "pop") e)
  | .both r o? =>
    let view ← (← tcLive r "pop").popLocals decls
    let o' ← ixcStep "pop" o? (·.pop decls.size)
    return { s with locals := s.locals.extract 0 keep, backend := .both (← tcRef view) o' }

/-- The sort level of a type in the scope (contract clause 3; fail closed). -/
def getLevel (s : AuxScope) (ty : Expr) : KBridgeM Level := do
  match s.backend with
  | .tc r => (← tcLive r "getLevel").getLevel ty
  | .ixc o =>
    bumpIxc fun st => { st with queries := st.queries + 1 }
    match o.getLevel ty with
    | .ok (l, fast, _) =>
      bumpIxc fun st => { st with answered := st.answered + 1,
                                  ixcFast := st.ixcFast + (if fast then 1 else 0) }
      return l
    | .error e =>
      bumpIxc fun st => (st.sample s!"getLevel refused: {e}") |> fun st =>
        { st with refused := st.refused + 1 }
      throwBridge (.kernel (.ixc "getLevel") e)
  | .both r o? =>
    let view ← tcLive r "getLevel"
    let tcFast := (← view.tryInferAppSortLevel ty).isSome
    let t ← view.getLevel ty
    bumpIxc fun st => { st with queries := st.queries + 1,
                                tcFast := st.tcFast + (if tcFast then 1 else 0) }
    let some o := o? | do
      bumpIxc fun st => { st with refused := st.refused + 1 }
      return t
    match o.getLevel ty with
    | .ok (l, fast, _) =>
      let same := Ix.Compile.ExactKey.levelEq l t
      bumpIxc fun st =>
        let st := { st with answered := st.answered + 1,
                            ixcFast := st.ixcFast + (if fast then 1 else 0),
                            equal := st.equal + (if same then 1 else 0),
                            differ := st.differ + (if same then 0 else 1) }
        if same then st else
          st.sample s!"differ (tcFast {tcFast}, ixcFast {fast}): Ix.Tc {levelText t}, \
            IxC {levelText l}"
      return if s.kernel.ixcMode? == some .fallback then l else t
    | .error e =>
      bumpIxc fun st => (st.sample s!"getLevel refused: {e}") |> fun st =>
        { st with refused := st.refused + 1 }
      return t

/-- The weak head normal form in the scope; `none` when the kernel gives no
    answer (clause 4). An IxC-only scope gives none. -/
def whnf? (s : AuxScope) (e : Expr) : KBridgeM (Option Expr) := do
  match s.backend with
  | .tc r | .both r _ => (← tcLive r "whnf").whnf? e
  | .ixc _ => return none

/-- Definitional equality in the scope; `none` when the kernel gives no
    answer (clause 5). An IxC-only scope gives none. -/
def isDefEq? (s : AuxScope) (a b : Expr) : KBridgeM (Option Bool) := do
  match s.backend with
  | .tc r | .both r _ => (← tcLive r "isDefEq").isDefEq? a b
  | .ixc _ => return none

/-- The type of a term in the scope, for decisions only; `none` when the
    kernel gives no answer (clause 6). An IxC-only scope gives none. -/
def inferType? (s : AuxScope) (e : Expr) : KBridgeM (Option Expr) := do
  match s.backend with
  | .tc r | .both r _ => (← tcLive r "inferType").inferLean e
  | .ixc _ => return none

/-- D-12's fail-open default for `whnf?`, named at each call site: the
    input when the kernel gives no answer (kept for parity; M3 and M4
    decide it per site). -/
def whnfOrInput (s : AuxScope) (e : Expr) : KBridgeM Expr :=
  return (← s.whnf? e).getD e

/-- D-12's fail-open default for `isDefEq?`: `false` when the kernel gives
    no answer. -/
def isDefEqOrFalse (s : AuxScope) (a b : Expr) : KBridgeM Bool :=
  return (← s.isDefEq? a b).getD false

end AuxScope

namespace AuxKernel

/-- The elimination decision for a block's original classes, in an expanded
    block of `nFlat` members (clause 8). `Ix.Tc`'s on both arms. -/
def elimDecision (k : AuxKernel)
    (originals : Array (InductiveVal × Array ConstructorVal)) (nParams nFlat : Nat) :
    KBridgeM ElimDecision :=
  tcElimDecision originals nParams nFlat k.maps

/-- Admit the prelude constants the generators name (`PUnit`, `PProd`). -/
def admitPrelude (k : AuxKernel) : KBridgeM Unit :=
  ensurePreludeInKenvOf k.maps

/-- Admit source constants, in order. -/
def admitSource (k : AuxKernel) (names : Array Name) (mode : AdmitMode := .full) :
    KBridgeM Unit := do
  let maps := k.maps
  for name in names do
    match mode with
    | .full => ensureInKenvOf name maps
    | .prewarm => ensureInKenvOfPrewarm name maps

/-- Admit generated constants (canonical `.below` families), so later
    queries naming them see the generated declarations (clause 9). `Ix.Tc`'s
    on both arms (IxC's inductive half is AuxGen M2b's). -/
def admitGenerated (k : AuxKernel) (consts : Array BelowConstant) : KBridgeM Unit :=
  tcAdmitBelow consts k.maps

/-- **The block's own canonical flat block**, from its canonical classes
    (restricted to Lean's `all`), Lean's `all` and its canonical recursors,
    before `.below` asks (AuxGen M2a): `Ix.Tc` needs nothing; the IxC arm
    installs it when the block's layout is not Lean's, and its scopes then
    read terms through σ. A refusal is counted, and fails the block under
    `failClosed`. -/
def withFlatBlock (k : AuxKernel) (classes : Array (Array Name)) (originalAll : Array Name)
    (canonicalRecs : Array (Name × RecursorVal)) : KBridgeM AuxKernel := do
  match k with
  | .tc _ => return k
  | .ixc maps o =>
    match o.withFlat classes originalAll canonicalRecs with
    | .ok none => return k
    | .ok (some o') =>
      bumpIxc fun st => { st with flatInstalled := st.flatInstalled + 1 }
      return .ixc maps o'
    | .error e =>
      bumpIxc fun st => (st.sample s!"flat block: {e}") |> fun st =>
        { st with flatRefused := st.flatRefused + 1 }
      if o.mode == .failClosed then throwBridge (.kernel (.ixc "flat block") e)
      return k

end AuxKernel

end Ix.AuxGen

end
