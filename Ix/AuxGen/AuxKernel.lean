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
  in the modes `shadow`, `fallback`, `failClosed`, `fallbackEager`; below);
  since M2b the compile driver gives a safe block's tail the `ixc` arm in
  `fallback`, and since M3 `.brecOn`'s scopes ask it too.

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

  ## The IxC arm (AuxGen M2a; the compile driver's since M2b)

  `ixc maps oracle` is `Ix.Tc` over `maps` for every generator, except the
  scopes a generator opens with `route := .below` (`.below`'s two scopes) or
  `route := .brecOn` (`.brecOn`'s three, AuxGen M3), which ask IxC Source
  mode through `oracle` (`Ix.AuxGen.Oracle`), in the oracle's mode
  (`IxcMode`):
  * `shadow`: both kernels answer every question; `Ix.Tc`'s answer is used.
  * `fallback` (production's mode; lazy since AuxGen M3): IxC first;
    `Ix.Tc` is asked only where IxC refuses (its scope is still opened,
    pushed and popped).
  * `failClosed`: IxC alone; a refusal fails the block.
  * `fallbackEager` (M2b's production mode, a measurement since M3): both
    answer; IxC's answer is used where it answers.

  The arm only calls the oracle's closures (`Ix.AuxGen.Oracle`'s
  docstring). Under `shadow` and `fallbackEager` the `Ix.Tc` scope is opened,
  pushed, popped and asked exactly as on the `Ix.Tc` arm, so `Ix.Tc`'s
  environment evolves as there; under `fallback` it is asked only behind a
  refusal. Each question is counted in `AuxKernelCtx.ixcStats`.

  Before `.below`, the tail asks the kernel to install the block's own
  canonical flat block (`withFlatBlock`): `Ix.Tc` needs nothing; IxC
  installs it when the block's layout is not Lean's, so `.below`'s terms
  read through σ.

  An IxC scope answers `getLevel`, `isDefEq?`, and (decision-grade: the
  result's binder names are anonymous, AuxGen M3) `whnf?` and `inferType?`;
  `.brecOn.eq`'s unit-like test is their only reader on these scopes.
-/
module
public import Ix.AuxGen.Kernel
public import Ix.AuxGen.Oracle
public import Ix.AuxGen.FlatBlock
public import Ix.AuxGen.LevelEgress
public import Ix.AuxGen.FastPaths
public section

namespace Ix.AuxGen

open Ix.CompileM (CompileM CompileError)

/-- The kernel AuxGen asks, with that kernel's environment. One value per
    AuxGen run (a compile block's tail, one decompile Pass-2 call). -/
inductive AuxKernel where
  /-- `Ix.Tc` over the bridge kenv; `maps` gives provisional addresses. -/
  | tc (maps : AddrMaps)
  /-- AuxGen M2: `Ix.Tc` over `maps`, and IxC Source mode through `oracle`
      for the scopes routed to it (`AuxRoute.below`). -/
  | ixc (maps : AddrMaps) (oracle : AuxOracle)

/-- The addresses `Ix.Tc` resolves through. -/
def AuxKernel.maps : AuxKernel → AddrMaps
  | .tc maps => maps
  | .ixc maps _ => maps

/-- Which generator opens a scope: `.below`'s (AuxGen M2) and `.brecOn`'s
    (AuxGen M3) scopes ask IxC on the `ixc` arm; the recursor generator's
    (AuxGen M4) do when the oracle says so (`AuxOracle.recursors`,
    production's since M4b). -/
inductive AuxRoute where
  | tc
  | below
  /-- `.brecOn`'s scopes (AuxGen M3) -/
  | brecOn
  /-- the recursor generator's scopes (AuxGen M4): lazy, and `whnf` with
      names (`OracleScope.whnfNamed`) -/
  | recursor
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
  /-- `Ix.Tc`, and IxC beside it (`shadow`, `fallback`, `fallbackEager`);
      `none` once IxC refused the scope. -/
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
  /-- the generator that opened it -/
  route : AuxRoute := .tc

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
  | .ixc maps o, .below | .ixc maps o, .brecOn =>
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
  | .ixc maps o, .recursor =>
    if o.recursors then
      -- AuxGen M4: a lazy IxC scope; nothing is asked until a question
      -- escapes the fast paths, and a refusal surfaces there.
      checkScopeNames ctx lps
      let s := o.newLazyScope lps (oracleLocals ctx)
      if o.mode == .failClosed then
        return { kernel := k, levelParams := lps, locals := ctx, nOuter := ctx.size,
                 backend := .ixc s, route := .recursor }
      let view ← TcScopeSt.new ctx lps maps
      return { kernel := k, levelParams := lps, locals := ctx, nOuter := ctx.size,
               backend := .both (← tcRef view) (some s), route := .recursor }
    let view ← TcScopeSt.new ctx lps maps
    return { kernel := k, levelParams := lps, locals := ctx, nOuter := ctx.size,
             backend := .tc (← tcRef view) }
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
    if s.kernel.ixcMode? == some .fallback then
      bumpIxc fun st => { st with queries := st.queries + 1 }
      if let some o := o? then
        match o.getLevel ty with
        | .ok (l, fast, _) =>
          bumpIxc fun st => { st with answered := st.answered + 1,
                                      ixcFast := st.ixcFast + (if fast then 1 else 0) }
          return l
        | .error e =>
          bumpIxc fun st => (st.sample s!"getLevel refused: {e}") |> fun st =>
            { st with refused := st.refused + 1 }
      else bumpIxc fun st => { st with refused := st.refused + 1 }
      return ← (← tcLive r "getLevel").getLevel ty
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
      return if s.kernel.ixcMode? == some .fallbackEager then l else t
    | .error e =>
      bumpIxc fun st => (st.sample s!"getLevel refused: {e}") |> fun st =>
        { st with refused := st.refused + 1 }
      return t

/-- IxC's answer to an expression question (`inferType?`, `whnf?`) on a
    `both` scope, counted: `none` when IxC refuses (or refused the scope). -/
private def ixcExprAnswer (op : String) (o? : Option OracleScope)
    (ask : OracleScope → Except String (Expr × OracleScope)) : KBridgeM (Option Expr) := do
  bumpIxc fun st => { st with exprQueries := st.exprQueries + 1 }
  let some o := o? | do
    bumpIxc fun st => { st with refused := st.refused + 1 }
    return none
  match ask o with
  | .ok (e, _) =>
    bumpIxc fun st => { st with exprAnswered := st.exprAnswered + 1 }
    return some e
  | .error err =>
    bumpIxc fun st => (st.sample s!"{op} refused: {err}") |> fun st =>
      { st with refused := st.refused + 1 }
    return none

/-- An IxC-only scope's answer to an expression question (`failClosed`): a
    refusal fails the block. -/
private def ixcExprOnly (op : String) (o : OracleScope)
    (ask : OracleScope → Except String (Expr × OracleScope)) : KBridgeM (Option Expr) := do
  bumpIxc fun st => { st with exprQueries := st.exprQueries + 1 }
  match ask o with
  | .ok (e, _) =>
    bumpIxc fun st => { st with exprAnswered := st.exprAnswered + 1 }
    return some e
  | .error err =>
    bumpIxc fun st => (st.sample s!"{op} refused: {err}") |> fun st =>
      { st with refused := st.refused + 1 }
    throwBridge (.kernel (.ixc op) err)

/-- A term head, for a sample line. -/
def headLabel : Expr → String
  | .const n _ _ => n.pretty
  | .fvar n _ => s!"fvar {n.pretty}"
  | .sort .. => "sort"
  | .forallE .. => "forall"
  | .lam .. => "lambda"
  | .letE .. => "let"
  | .proj n i _ _ => s!"proj {n.pretty}.{i}"
  | .lit .. => "literal"
  | .mdata .. => "mdata"
  | _ => "other"

/-- The first difference between two terms, by kind (AuxGen M4's shadow):
`"binder name"`, `"binder info"`, `"level"`, `"constant"` or `"shape"`;
`none` when they are equal. -/
def diffKind (a b : Expr) : Option String :=
  if Ix.Compile.ExactKey.exprEq a b then none else
  match a, b with
  | .forallE n t c bi _, .forallE m u d bj _ | .lam n t c bi _, .lam m u d bj _ =>
    if !Ix.Compile.ExactKey.nameEq n m then some "binder name"
    else if bi != bj then some "binder info"
    else (diffKind t u).orElse fun _ => diffKind c d
  | .letE n t v c _ _, .letE m u w d _ _ =>
    if !Ix.Compile.ExactKey.nameEq n m then some "binder name"
    else ((diffKind t u).orElse fun _ => diffKind v w).orElse fun _ => diffKind c d
  | .app f x _, .app g y _ => (diffKind f g).orElse fun _ => diffKind x y
  | .sort _ _, .sort _ _ => some "level"
  | .const n us _, .const m vs _ =>
    if !Ix.Compile.ExactKey.nameEq n m then some "constant"
    else if us.size != vs.size then some "shape" else some "level"
  | .proj n i x _, .proj m j y _ =>
    if !Ix.Compile.ExactKey.nameEq n m || i != j then some "constant" else diffKind x y
  | _, _ => some "shape"

/-- Count how IxC answered a named `whnf` (AuxGen M4). -/
private def bumpHow (how : WhnfHow) : KBridgeM Unit :=
  bumpIxc fun st => match how with
    | .stuck => { st with recStuck := st.recStuck + 1 }
    | .same => { st with recSame := st.recSame + 1, recForced := st.recForced + 1 }
    | .replayed => { st with recReplayed := st.recReplayed + 1, recForced := st.recForced + 1 }

/-- An IxC refusal of a named `whnf`, counted. -/
private def bumpRecRefused (err : String) : KBridgeM Unit :=
  bumpIxc fun st => (st.sample s!"rec whnf refused: {err}") |> fun st =>
    { st with recRefused := st.recRefused + 1, recForced := st.recForced + 1 }

/-- **The recursor generator's `whnf`** on a `recursor` scope (AuxGen M4): IxC's
named answer (`OracleScope.whnfNamed`); against `Ix.Tc`'s restored answer
under `shadow` and `fallbackEager` (`named`: the result reaches generated
binders; otherwise a decision site's); IxC first and `Ix.Tc` behind a
refusal under `fallback`; IxC alone under `failClosed`. -/
def whnfRec? (s : AuxScope) (e : Expr) (named : Bool) : KBridgeM (Option Expr) := do
  match s.backend with
  | .tc r => (← tcLive r "whnf").whnf? e
  | .ixc o =>
    bumpIxc fun st => { st with recWhnf := st.recWhnf + 1 }
    match o.whnfNamed e with
    | .ok (w, how, _) =>
      bumpHow how
      return some w
    | .error err =>
      bumpRecRefused err
      throwBridge (.kernel (.ixc "whnf") err)
  | .both r o? =>
    bumpIxc fun st => { st with recWhnf := st.recWhnf + 1 }
    if s.kernel.ixcMode? == some .fallback then
      if let some o := o? then
        match o.whnfNamed e with
        | .ok (w, how, _) =>
          bumpHow how
          return some w
        | .error err => bumpRecRefused err
      else bumpRecRefused "no scope"
      return ← (← tcLive r "whnf").whnf? e
    let t ← (← tcLive r "whnf").whnf? e
    let some o := o? | do
      bumpRecRefused "no scope"
      return t
    match o.whnfNamed e with
    | .ok (w, how, _) =>
      bumpHow how
      let kind := match t with
        | some t => diffKind t w
        | none => some "Ix.Tc gave no answer"
      match kind with
      | none => bumpIxc fun st => { st with recEqual := st.recEqual + 1 }
      | some k =>
        bumpIxc fun st =>
          let st := { st with recDiffer := st.recDiffer + 1 }
          let st := if !named then { st with recDecisionDiffer := st.recDecisionDiffer + 1 }
            else if k == "binder name" then { st with recDiffName := st.recDiffName + 1 }
            else if k == "binder info" then { st with recDiffInfo := st.recDiffInfo + 1 }
            else if k == "level" then { st with recDiffLevel := st.recDiffLevel + 1 }
            else { st with recDiffOther := st.recDiffOther + 1 }
          st.sample s!"rec whnf differ ({k}, {repr how}, {if named then "named" else "decision"} \
            site): head {headLabel (decomposeApps (stripMdataRef e)).1}"
      return if s.kernel.ixcMode? == some .fallbackEager then some w else t
    | .error err =>
      bumpRecRefused err
      return t

/-- AuxGen M4: a `recursor` scope on IxC, where `findRecTarget` skips the
    Phase 2 of a field that names no member of the block's classes. -/
def skipsUnmentioned (s : AuxScope) : Bool :=
  s.route == .recursor && !(s.backend matches .tc _)

/-- AuxGen M4: whether `Ix.Tc` still decides a skipped field (`shadow`,
    `fallbackEager`), so a disagreement is counted. -/
def checksSkips (s : AuxScope) : Bool :=
  s.skipsUnmentioned && (s.kernel.ixcMode? == some .shadow || s.kernel.ixcMode? == some .fallbackEager)

/-- `Ix.Tc`'s `whnf` alone, the input when it gives no answer (AuxGen M4's
    check of a skipped field); the input on an IxC-only scope. -/
def whnfTcOrInput (s : AuxScope) (e : Expr) : KBridgeM Expr := do
  match s.backend with
  | .tc r | .both r _ => return ((← (← tcLive r "whnf").whnf? e).getD e)
  | .ixc _ => return e

/-- `Ix.Tc`'s cache warmed with `whnf e`, the result discarded
    (`findRecTarget`'s pre-warm, which only `Ix.Tc`'s display-name aliasing
    needs); nothing on IxC. -/
def warm (s : AuxScope) (e : Expr) : KBridgeM Unit := do
  match s.backend with
  | .tc r | .both r _ => discard <| (← tcLive r "whnf").whnf? e
  | .ixc _ => pure ()

/-- The weak head normal form in the scope; `none` when the kernel gives no
    answer (clause 4). IxC's answer is decision-grade (AuxGen M3: its binder
    names are anonymous; only `.brecOn.eq`'s unit-like test reads it). -/
def whnf? (s : AuxScope) (e : Expr) : KBridgeM (Option Expr) := do
  if s.route == .recursor then return ← s.whnfRec? e true
  match s.backend with
  | .tc r => (← tcLive r "whnf").whnf? e
  | .ixc o => ixcExprOnly "whnf" o (·.whnf e)
  | .both r o? =>
    if s.kernel.ixcMode? == some .fallback then
      if let some w ← ixcExprAnswer "whnf" o? (·.whnf e) then return some w
      return ← (← tcLive r "whnf").whnf? e
    let t ← (← tcLive r "whnf").whnf? e
    let i? ← ixcExprAnswer "whnf" o? (·.whnf e)
    return if s.kernel.ixcMode? == some .fallbackEager then i?.orElse fun _ => t else t

/-- Definitional equality in the scope; `none` when the kernel gives no
    answer (clause 5). On a `both` scope the two kernels' answers are
    compared (AuxGen M3). -/
def isDefEq? (s : AuxScope) (a b : Expr) : KBridgeM (Option Bool) := do
  match s.backend with
  | .tc r => (← tcLive r "isDefEq").isDefEq? a b
  | .ixc o =>
    bumpIxc fun st => { st with decisions := st.decisions + 1 }
    match o.isDefEq a b with
    | .ok (q, _) => return some q
    | .error err =>
      bumpIxc fun st => (st.sample s!"isDefEq refused: {err}") |> fun st =>
        { st with refused := st.refused + 1 }
      throwBridge (.kernel (.ixc "isDefEq") err)
  | .both r o? =>
    if s.kernel.ixcMode? == some .fallback then
      bumpIxc fun st => { st with decisions := st.decisions + 1 }
      if let some o := o? then
        match o.isDefEq a b with
        | .ok (q, _) => return some q
        | .error err =>
          bumpIxc fun st => (st.sample s!"isDefEq refused: {err}") |> fun st =>
            { st with refused := st.refused + 1 }
      else bumpIxc fun st => { st with refused := st.refused + 1 }
      return ← (← tcLive r "isDefEq").isDefEq? a b
    let t ← (← tcLive r "isDefEq").isDefEq? a b
    bumpIxc fun st => { st with decisions := st.decisions + 1 }
    let some o := o? | do
      bumpIxc fun st => { st with refused := st.refused + 1 }
      return t
    match o.isDefEq a b with
    | .ok (q, _) =>
      let same := t == some q
      bumpIxc fun st =>
        let st := { st with decisionsEqual := st.decisionsEqual + (if same then 1 else 0),
                            decisionsDiffer := st.decisionsDiffer + (if same then 0 else 1) }
        if same then st else st.sample s!"isDefEq differ: Ix.Tc {t}, IxC {q}"
      return if s.kernel.ixcMode? == some .fallbackEager then some q else t
    | .error err =>
      bumpIxc fun st => (st.sample s!"isDefEq refused: {err}") |> fun st =>
        { st with refused := st.refused + 1 }
      return t

/-- The type of a term in the scope, for decisions only; `none` when the
    kernel gives no answer (clause 6). IxC's answer is decision-grade, as
    `whnf?`'s. -/
def inferType? (s : AuxScope) (e : Expr) : KBridgeM (Option Expr) := do
  match s.backend with
  | .tc r => (← tcLive r "inferType").inferLean e
  | .ixc o => ixcExprOnly "inferType" o (·.infer e)
  | .both r o? =>
    if s.kernel.ixcMode? == some .fallback then
      if let some t ← ixcExprAnswer "inferType" o? (·.infer e) then return some t
      return ← (← tcLive r "inferType").inferLean e
    let t ← (← tcLive r "inferType").inferLean e
    let i? ← ixcExprAnswer "inferType" o? (·.infer e)
    return if s.kernel.ixcMode? == some .fallbackEager then i?.orElse fun _ => t else t

/-- D-12's fail-open default for `whnf?`, named at each call site: the
    input when the kernel gives no answer (kept for parity; M3 and M4
    decide it per site). On a `recursor` scope, `named` says whether the
    result reaches generated binders (AuxGen M4's shadow counts a decision
    site's differences apart). -/
def whnfOrInput (s : AuxScope) (e : Expr) (named : Bool := true) : KBridgeM Expr := do
  if s.route == .recursor then return (← s.whnfRec? e named).getD e
  return (← s.whnf? e).getD e

/-- D-12's fail-open default for `isDefEq?`: `false` when the kernel gives
    no answer. -/
def isDefEqOrFalse (s : AuxScope) (a b : Expr) : KBridgeM Bool :=
  return (← s.isDefEq? a b).getD false

end AuxScope

namespace AuxKernel

/-! ### The elimination decision on IxC (AuxGen M4)

`Ix.Tc`'s `RecM.getResultSortLevel` and `RecM.isLargeEliminator` (Lean's
`elim_only_at_universe_zero`), ported onto an IxC lazy scope: telescopes
peeled syntactically, through `whnf` where a head is stuck; levels by
`getLevel` (its `inferAppType` fast path first). IxC's acceptance of the
generated recursor (the canonical block, M4) validates the decision; the
shadow compares it with `Ix.Tc`'s. -/

/-- Always zero, whatever the parameters (`Ix.Tc`'s `isSemanticZero`, and
`univEq _ zero`). -/
def levelAlwaysZero : Level → Bool
  | .zero _ => true
  | .max a b _ => levelAlwaysZero a && levelAlwaysZero b
  | .imax _ b _ => levelAlwaysZero b
  | _ => false

/-- Never zero (`Ix.Tc`'s `KUniv.isNeverZero`). -/
def levelNeverZero : Level → Bool
  | .succ _ _ => true
  | .max a b _ => levelNeverZero a || levelNeverZero b
  | .imax _ b _ => levelNeverZero b
  | _ => false

/-- The decision's fresh local names. -/
private def elimLocal (s : String) (i : Nat) : Name :=
  Name.mkNat (Name.mkStr (Name.mkStr Name.mkAnon "_ixelim") s) i

/-- Peel one `∀` of `ty` into `sc` (through `whnf` when the head is not a
`∀`): the scope with the binder pushed, the body instantiated, the domain,
whether the service was needed; `none` when there is no `∀`. -/
private def elimPeel (sc : OracleScope) (ty : Expr) (name : Name) :
    Except String (Option (OracleScope × Expr × Expr × Bool)) := do
  let (w, forced) ← match ty with
    | .forallE .. => pure (ty, false)
    | _ => do
      let (w, how, _) ← sc.whnfNamed ty
      pure (w, how != .stuck)
  match w with
  | .forallE _ dom body _ _ =>
    let sc ← sc.push #[(name, dom)]
    return some (sc, instantiate1 body (Expr.mkFVar name), dom, forced)
  | _ => return none

/-- **The elimination decision from IxC's services**, and whether the
service was needed (a question escaped the fast paths). -/
def ixcElimDecision (o : AuxOracle) (originals : Array (InductiveVal × Array ConstructorVal))
    (nParams nFlat : Nat) : Except String (ElimDecision × Bool) := do
  let some (first, ctors0) := originals[0]? | throw "elimination: no class"
  let lps := first.cnst.levelParams
  let mut forced := false
  -- the result sort, after the parameters and indices
  let mut sc := o.newLazyScope lps #[]
  let mut ty := first.cnst.type
  for i in [0:nParams + first.numIndices] do
    match ← elimPeel sc ty (elimLocal "r" i) with
    | some (sc', body, _, f) =>
      sc := sc'
      ty := body
      forced := forced || f
    | none => throw s!"get_result_sort_level: expected {nParams + first.numIndices} foralls, \
        only found {i}"
  let w ← match ty with
    | .sort .. => pure ty
    | _ => do
      let (w, how, _) ← sc.whnfNamed ty
      forced := forced || how != .stuck
      pure w
  let .sort u _ := w | throw "get_result_sort_level: not a sort"
  let resultLevel := Egress.normalize u
  let isProp := levelAlwaysZero resultLevel
  if !levelNeverZero resultLevel && nFlat != 1 then
    return ({ isLarge := false, isProp }, forced)
  -- `isLargeEliminator`
  if levelNeverZero resultLevel then return ({ isLarge := true, isProp }, forced)
  if originals.size != 1 then return ({ isLarge := false, isProp }, forced)
  match ctors0.size with
  | 0 => return ({ isLarge := true, isProp }, forced)
  | 1 =>
    let some ctor := ctors0[0]? | throw "elimination: constructor"
    if ctor.numFields == 0 then return ({ isLarge := true, isProp }, forced)
    sc := o.newLazyScope lps #[]
    ty := ctor.cnst.type
    let mut nonTrivial : Array Nat := #[]
    let mut fields : Array Name := #[]
    for i in [0:nParams + ctor.numFields] do
      let name := elimLocal "f" i
      match ← elimPeel sc ty name with
      | some (sc', body, dom, f) =>
        forced := forced || f
        if i ≥ nParams then
          let (lvl, fast, _) ← sc.getLevel dom
          forced := forced || !fast
          if !levelAlwaysZero lvl then nonTrivial := nonTrivial.push (i - nParams)
          fields := fields.push name
        sc := sc'
        ty := body
      | none => break
    let (_, retArgs) := decomposeApps ty
    let isLarge := nonTrivial.all fun fi =>
      match fields[fi]? with
      | some target => retArgs.any fun arg => match arg with
        | .fvar n _ => Ix.Compile.ExactKey.nameEq n target
        | _ => false
      | none => false
    return ({ isLarge, isProp }, forced)
  | _ => return ({ isLarge := false, isProp }, forced)

/-- The elimination decision for a block's original classes, in an expanded
    block of `nFlat` members (clause 8). `Ix.Tc`'s, except on the `ixc` arm
    with `AuxOracle.recursors` (production's since AuxGen M4b): IxC's
    (`ixcElimDecision`), compared with `Ix.Tc`'s under `shadow` and
    `fallbackEager`, `Ix.Tc`'s behind a refusal under `fallback`, alone under
    `failClosed`. -/
def elimDecision (k : AuxKernel)
    (originals : Array (InductiveVal × Array ConstructorVal)) (nParams nFlat : Nat) :
    KBridgeM ElimDecision := do
  match k with
  | .ixc maps o =>
    if !o.recursors then return ← tcElimDecision originals nParams nFlat maps
    bumpIxc fun st => { st with elim := st.elim + 1 }
    let ixc := ixcElimDecision o originals nParams nFlat
    if let .ok (_, forced) := ixc then
      if forced then bumpIxc fun st => { st with recForced := st.recForced + 1 }
    let refused (e : String) : KBridgeM Unit :=
      bumpIxc fun st => (st.sample s!"elimination refused: {e}") |> fun st =>
        { st with elimRefused := st.elimRefused + 1 }
    -- `Ix.Tc`'s later users of the block read the kenv inserts its decision
    -- makes; keep them where `Ix.Tc` does not decide.
    if o.mode == .failClosed || o.mode == .fallback then
      discard <| tcElimAdmit originals nParams maps
    match o.mode with
    | .failClosed =>
      match ixc with
      | .ok (d, _) => return d
      | .error e =>
        refused e
        throwBridge (.kernel (.ixc "elimination") e)
    | .fallback =>
      match ixc with
      | .ok (d, _) => return d
      | .error e =>
        refused e
        tcElimDecision originals nParams nFlat maps
    | _ =>
      let t ← tcElimDecision originals nParams nFlat maps
      match ixc with
      | .ok (d, _) =>
        if d == t then bumpIxc fun st => { st with elimEqual := st.elimEqual + 1 }
        else bumpIxc fun st => (st.sample s!"elimination differ: Ix.Tc \
            (large {t.isLarge}, prop {t.isProp}), IxC (large {d.isLarge}, prop {d.isProp})") |>
          fun st => { st with elimDiffer := st.elimDiffer + 1 }
        return if o.mode == .fallbackEager then d else t
      | .error e =>
        refused e
        return t
  | .tc maps => tcElimDecision originals nParams nFlat maps

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
    queries naming them see the generated declarations (clause 9): `Ix.Tc`'s
    kenv on both arms, and on the `ixc` arm IxC's environment too (AuxGen M3,
    `AuxOracle.admitBelow`), whose result is the kernel the later generators
    ask (`.brecOn`). IxC takes the Type-level definitions only: the
    Prop-level `.brecOn` asks the kernel nothing, so a Prop-level family
    would only cost its block a fold of the service. An IxC refusal is
    counted; its questions then refuse, and `fallback` answers them by
    `Ix.Tc`. -/
def admitGenerated (k : AuxKernel) (consts : Array BelowConstant) : KBridgeM AuxKernel := do
  tcAdmitBelow consts k.maps
  match k with
  | .tc _ => return k
  | .ixc maps o =>
    let defs := consts.filterMap fun | .defn d => some d | .indc _ => none
    if defs.isEmpty then return k
    match o.admitBelow defs with
    | .ok (o', ok, bad) =>
      bumpIxc fun st => { st with belowAdmitted := st.belowAdmitted + ok,
                                  belowRefused := st.belowRefused + bad }
      return .ixc maps o'
    | .error e =>
      bumpIxc fun st => (st.sample s!"admit .below: {e}") |> fun st =>
        { st with belowRefused := st.belowRefused + defs.size }
      return k

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

/-- Two recursors equal as declarations, names and binder data included. -/
def sameRecursor (a b : RecursorVal) : Bool :=
  open Ix.Compile.ExactKey in
  nameEq a.cnst.name b.cnst.name && a.cnst.levelParams.isEqv b.cnst.levelParams nameEq
    && exprEq a.cnst.type b.cnst.type && a.all.isEqv b.all nameEq
    && a.numParams == b.numParams && a.numIndices == b.numIndices
    && a.numMotives == b.numMotives && a.numMinors == b.numMinors
    && a.k == b.k && a.isUnsafe == b.isUnsafe && a.rules.size == b.rules.size
    && (a.rules.zip b.rules).all fun (r, s) =>
      nameEq r.ctor s.ctor && r.nfields == s.nfields && exprEq r.rhs s.rhs

/-- **The canonical block checked by Source mode** (AuxGen M4a; production's
since M4b, with `AuxOracle.recursors`), right after the recursors are
generated: for a block whose layout is not Lean's, its canonical flat block,
the generated recursors included, installed through σ (`withFlatBlock`;
IxC's install is the check, counted as `flat` installed or refused); for a
block whose layout is Lean's, each generated recursor compared with Lean's
own (`leanRecSame`, `leanRecDiffer`), whose acceptance is the input's. The
kernel after it, and whether the check ran (then `.below` needs no second
install). -/
def checkCanonicalBlock (k : AuxKernel) (classes : Array (Array Name))
    (originalAll : Array Name) (canonicalRecs : Array (Name × RecursorVal)) :
    KBridgeM (AuxKernel × Bool) := do
  match k with
  | .tc _ => return (k, false)
  | .ixc _ o =>
    if !o.recursors then return (k, false)
    let nClasses := classes.size
    let auxNames := (canonicalRecs.extract nClasses canonicalRecs.size).map (·.1)
    let leanNested ← match originalAll[0]? with
      | some n => do
        match ← lookupConst? n with
        | some (.inductInfo v) => pure v.numNested
        | _ => pure 0
      | none => pure 0
    if Flat.needed classes originalAll auxNames leanNested then
      return (← k.withFlatBlock classes originalAll canonicalRecs, true)
    for (n, rv) in canonicalRecs do
      match ← lookupConst? n with
      | some (.recInfo lean) =>
        if sameRecursor rv lean then
          bumpIxc fun st => { st with leanRecSame := st.leanRecSame + 1 }
        else
          bumpIxc fun st => (st.sample s!"canonical recursor differs from Lean's: {n.pretty}") |>
            fun st => { st with leanRecDiffer := st.leanRecDiffer + 1 }
      | _ =>
        bumpIxc fun st => (st.sample s!"no Lean recursor: {n.pretty}") |>
          fun st => { st with leanRecDiffer := st.leanRecDiffer + 1 }
    return (k, true)

end AuxKernel

end Ix.AuxGen

end
