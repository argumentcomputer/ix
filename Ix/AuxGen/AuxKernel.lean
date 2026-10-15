/-
  Ix.AuxGen.AuxKernel: the kernel interface AuxGen's generators ask
  (AuxGen M0, CQ2.16).

  The generators (`Recursor`, `Below`, `BRecOn`, `Patches`, `CompileAux`)
  need a kernel for a handful of questions: the sort level of a type, the
  weak head normal form of a term, definitional equality, the type of a term
  (for a decision), the block's elimination decision, and an environment
  that holds the constants those questions name. This module states those
  questions as an interface over a closed sum of backends. M0 has one
  backend, `Ix.Tc` through the bridge (`Ix.AuxGen.Kernel`); AuxGen M1 adds
  IxC's Source mode beside it (`ixc`, `ixcFallback`, `shadow`), at the two
  construction points `compileMutualAuxTail` and the decompile driver's
  `runK`.

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
     block's original classes: the WHNF-peeled result sort, with the
     mutual-Prop rule. It fails closed with the `invalidMutualBlock` texts.
     It may supersede scopes, and does in `Ix.Tc`.
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
-/
module
public import Ix.AuxGen.Kernel
public section

namespace Ix.AuxGen

open Ix.CompileM (CompileM CompileError)

/-- The kernel AuxGen asks, with that kernel's environment. One value per
    AuxGen run (a compile block's tail, one decompile Pass-2 call). -/
inductive AuxKernel where
  /-- `Ix.Tc` over the bridge kenv; `maps` gives provisional addresses. -/
  | tc (maps : AddrMaps)

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

/-- A local context as a value. It denotes `(levelParams, locals)`. -/
structure AuxScope where
  kernel : AuxKernel
  levelParams : Array Name
  /-- Outermost first: the outer context, then the pushed locals. -/
  locals : Array LocalDecl
  /-- The locals from `new`; `pop` cannot remove them. -/
  nOuter : Nat
  backend : AuxScopeBackend

namespace AuxScope

/-- The scope's depth: its number of locals. -/
def depth (s : AuxScope) : Nat := s.locals.size

/-- The current `Ix.Tc` reference for `view`. -/
private def tcRef (view : TcScopeSt) : KBridgeM TcScopeRef := do
  let ctx ← get
  return { view, epoch := ctx.scopeEpoch, ctxId := ctx.tcState.ctxId }

/-- The bridge view of a scope value, if its backend can serve it. `Ix.Tc`
    serves a value while the kernel context it denotes is live: no newer
    scope or elimination decision replaced the type checker (the epoch), and
    the type checker's context is the one the value left (`ctxId`, which
    `Ix.Tc` restores on every outcome of a query). Depth alone would not do:
    after `push [x]`, `pop`, `push [y]` the depth matches, but `x` would be
    answered as `y`. Otherwise the value is refused (`staleScope`). This
    only reads state. -/
def live? (s : AuxScope) (op : String) : KBridgeM TcScopeSt := do
  match s.backend with
  | .tc r =>
    let ctx ← get
    if r.epoch == ctx.scopeEpoch && r.ctxId == ctx.tcState.ctxId then
      return r.view
    throwBridge (.staleScope op)

/-- Open a scope over `ctx` with level parameters `lps`. -/
def new (k : AuxKernel) (ctx : Array LocalDecl) (lps : Array Name) :
    KBridgeM AuxScope := do
  match k with
  | .tc maps =>
    let view ← TcScopeSt.new ctx lps maps
    return { kernel := k, levelParams := lps, locals := ctx, nOuter := ctx.size,
             backend := .tc (← tcRef view) }

/-- Push a telescope onto the scope. -/
def push (s : AuxScope) (decls : Array LocalDecl) : KBridgeM AuxScope := do
  let view ← (← s.live? "push").pushLocals decls
  return { s with locals := s.locals ++ decls, backend := .tc (← tcRef view) }

/-- Pop the most recently pushed telescope `decls`. -/
def pop (s : AuxScope) (decls : Array LocalDecl) : KBridgeM AuxScope := do
  -- `popLocals` refuses a pop beyond the pushed locals or out of order, so
  -- the truncation below removes exactly `decls`.
  let view ← (← s.live? "pop").popLocals decls
  return { s with locals := s.locals.extract 0 (s.locals.size - decls.size),
                  backend := .tc (← tcRef view) }

/-- The sort level of a type in the scope (contract clause 3; fail closed). -/
def getLevel (s : AuxScope) (ty : Expr) : KBridgeM Level := do
  (← s.live? "getLevel").getLevel ty

/-- The weak head normal form in the scope; `none` when the kernel gives no
    answer (clause 4). -/
def whnf? (s : AuxScope) (e : Expr) : KBridgeM (Option Expr) := do
  (← s.live? "whnf").whnf? e

/-- Definitional equality in the scope; `none` when the kernel gives no
    answer (clause 5). -/
def isDefEq? (s : AuxScope) (a b : Expr) : KBridgeM (Option Bool) := do
  (← s.live? "isDefEq").isDefEq? a b

/-- The type of a term in the scope, for decisions only; `none` when the
    kernel gives no answer (clause 6). -/
def inferType? (s : AuxScope) (e : Expr) : KBridgeM (Option Expr) := do
  (← s.live? "inferType").inferLean e

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

/-- The elimination decision for a block's original classes (clause 8). -/
def elimDecision (k : AuxKernel)
    (originals : Array (InductiveVal × Array ConstructorVal)) (nParams : Nat) :
    KBridgeM ElimDecision :=
  match k with
  | .tc maps => tcElimDecision originals nParams maps

/-- Admit the prelude constants the generators name (`PUnit`, `PProd`). -/
def admitPrelude (k : AuxKernel) : KBridgeM Unit :=
  match k with
  | .tc maps => ensurePreludeInKenvOf maps

/-- Admit source constants, in order. -/
def admitSource (k : AuxKernel) (names : Array Name) (mode : AdmitMode := .full) :
    KBridgeM Unit :=
  match k with
  | .tc maps =>
    for name in names do
      match mode with
      | .full => ensureInKenvOf name maps
      | .prewarm => ensureInKenvOfPrewarm name maps

/-- Admit generated constants (canonical `.below` families), so later
    queries naming them see the generated declarations (clause 9). -/
def admitGenerated (k : AuxKernel) (consts : Array BelowConstant) : KBridgeM Unit :=
  match k with
  | .tc maps => tcAdmitBelow consts maps

end AuxKernel

end Ix.AuxGen
