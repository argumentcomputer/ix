import Ix.Tc.Verify.Inductive.OccurrenceValidation

/-!
# Production positivity traversal

E2c must account for the recursive control flow that reaches occurrence
validation, rather than assuming that a particular constructor field was
already reduced to an active-family application.  This module starts that
assembly at the production `checkPositivityDomainFuel` entry point.

The first theorem records the root-free early return.  The second exposes the
exact active-family callback reached after WHNF and spine collection, including
its real intermediate checker state.  The final theorem composes that equation
with the oracle-free occurrence invariant from `OccurrenceValidation`.
-/

namespace Ix.Tc
namespace RecM

private theorem runTryCatch (body : RecM m α)
    (handler : TcError m → RecM m α) (methods : Methods m) :
    (tryCatch body handler).run methods =
      tryCatch (body.run methods) (fun err => (handler err).run methods) := by
  rfl

private theorem runModify (f : TcState m → TcState m)
    (methods : Methods m) :
    (modify f : RecM m Unit).run methods = (modify f : TcM m Unit) := by
  rfl

private theorem runExceptUnit (result : Except (TcError m) Unit)
    (methods : Methods m) :
    (match result with
      | .ok () => (pure () : RecM m Unit)
      | .error err => throw err).run methods =
    (match result with
      | .ok () => (pure () : TcM m Unit)
      | .error err => throw err) := by
  cases result with
  | ok value => cases value; rfl
  | error _ => rfl

/-- Verification-only spelling of the explicit scope restoration used by the
production positivity loops after a binder has been opened. -/
private def restoreLctxResultTc (saved : Nat) (x : TcM m Unit) : TcM m Unit := do
  let result ←
    try
      x
      pure (Except.ok ())
    catch e =>
      pure (Except.error e)
  modify fun s => { s with lctx := s.lctx.truncate saved }
  match result with
  | .ok () => return ()
  | .error e => throw e

private theorem restoreLctxResultTc_success
    (saved : Nat) (x : TcM m Unit) (before final : TcState m)
    (hrun : restoreLctxResultTc saved x before = .ok () final) :
    ∃ after, x before = .ok () after ∧
      final = { after with lctx := after.lctx.truncate saved } := by
  unfold restoreLctxResultTc at hrun
  change EStateM.bind
    (EStateM.tryCatch
      (EStateM.bind x (fun _ => pure (Except.ok ())))
      (fun e => pure (Except.error e)))
    _ before = .ok () final at hrun
  unfold EStateM.bind EStateM.tryCatch at hrun
  cases hx : x before with
  | error _ _ =>
      simp only [hx] at hrun
      contradiction
  | ok value after =>
      cases value
      simp only [hx] at hrun
      change EStateM.Result.ok ()
          { after with lctx := after.lctx.truncate saved } =
        EStateM.Result.ok () final at hrun
      cases hrun
      exact ⟨after, rfl, rfl⟩

/-- Verification-only spelling of production's protected action followed by
local-context suffix restoration. -/
def withLctxRestoration (saved : Nat) (x : RecM m Unit) : RecM m Unit := do
  let result ←
    try
      x
      pure (Except.ok ())
    catch e =>
      pure (Except.error e)
  modify fun s => { s with lctx := s.lctx.truncate saved }
  match result with
  | .ok () => return ()
  | .error e => throw e

private theorem withLctxRestoration_run
    (saved : Nat) (x : RecM m Unit) (methods : Methods m)
    (state : TcState m) :
    (withLctxRestoration saved x).run methods state =
      restoreLctxResultTc saved (x.run methods) state := by
  unfold withLctxRestoration restoreLctxResultTc
  simp only [ReaderT.run_bind, runTryCatch]
  simp only [ReaderT.run_pure, runModify, runExceptUnit]

theorem withLctxRestoration_success
    (saved : Nat) (x : RecM m Unit) (methods : Methods m)
    (before final : TcState m)
    (hrun : (withLctxRestoration saved x).run methods before = .ok () final) :
    ∃ after, x.run methods before = .ok () after ∧
      final = { after with lctx := after.lctx.truncate saved } := by
  rw [withLctxRestoration_run] at hrun
  exact restoreLctxResultTc_success saved (x.run methods) before final hrun

/-- A field domain that does not mention the original block takes the
production early return and leaves the checker state unchanged. -/
theorem checkPositivityDomainFuel_rootFree
    {fuel : Nat} {dom : KExpr m} {groups : Array (PositivityGroup m)}
    {activeAddrs : Array Address} {methods : Methods m}
    {state : TcState m} {rootGroup : PositivityGroup m}
    (hroot : groups[0]? = some rootGroup)
    (hfree : exprMentionsAnyAddr dom rootGroup.addrs = false) :
    (checkPositivityDomainFuel (fuel + 1) dom groups activeAddrs).run
        methods state = .ok () state := by
  simp [checkPositivityDomainFuel, hroot, hfree]
  rfl

/-- If production positivity succeeds through the direct active-family branch,
the exact recursive-application validator succeeds from the state produced by
WHNF to the traversal's final state.

The spine equality also rules out the preceding forall branch.  The proof
performs that discrimination explicitly so the theorem does not need a
separate, redundant "WHNF is not a forall" premise. -/
theorem checkPositivityDomainFuel_direct
    {fuel : Nat} {dom w : KExpr m}
    {groups : Array (PositivityGroup m)} {activeAddrs : Array Address}
    {methods : Methods m} {initial afterWhnf final : TcState m}
    {rootGroup : PositivityGroup m} {id : KId m}
    {us : Array (KUniv m)} {info : ExprInfo m}
    {args : Array (KExpr m)}
    (hroot : groups[0]? = some rootGroup)
    (hmentions : exprMentionsAnyAddr dom rootGroup.addrs = true)
    (hwhnf : (whnf dom).run methods initial = .ok w afterWhnf)
    (hspine : w.collectSpine = (.const id us info, args))
    (hactive : rootGroup.addrs.contains id.addr = true)
    (hrun :
      (checkPositivityDomainFuel (fuel + 1) dom groups activeAddrs).run
        methods initial = .ok () final) :
    (checkPositiveRecursiveApplication id us args groups rootGroup.addrs).run
        methods afterWhnf = .ok () final := by
  unfold checkPositivityDomainFuel at hrun
  simp only [hroot, hmentions, Bool.not_true, Bool.false_eq_true, if_false]
    at hrun
  rw [ReaderT.run_bind] at hrun
  change EStateM.bind ((whnf dom).run methods) _ initial = _ at hrun
  unfold EStateM.bind at hrun
  rw [hwhnf] at hrun
  cases w <;> simp_all [KExpr.collectSpine, KExpr.collectSpine.go]

/-- Rebuild a successful field-domain traversal at any positive fuel from the
exact direct recursive-application run.  The inner fuel is unused on this
branch; making the converse explicit lets concrete constructor traces align
with their enclosing validator's actual fuel without re-executing the
recursive-application checker. -/
theorem checkPositivityDomainFuel_direct_run
    {fuel : Nat} {dom w : KExpr m}
    {groups : Array (PositivityGroup m)} {activeAddrs : Array Address}
    {methods : Methods m} {initial afterWhnf final : TcState m}
    {rootGroup : PositivityGroup m} {id : KId m}
    {us : Array (KUniv m)} {info : ExprInfo m}
    {args : Array (KExpr m)}
    (hroot : groups[0]? = some rootGroup)
    (hmentions : exprMentionsAnyAddr dom rootGroup.addrs = true)
    (hwhnf : (whnf dom).run methods initial = .ok w afterWhnf)
    (hspine : w.collectSpine = (.const id us info, args))
    (hactive : rootGroup.addrs.contains id.addr = true)
    (hdirect :
      (checkPositiveRecursiveApplication id us args groups rootGroup.addrs).run
        methods afterWhnf = .ok () final) :
    (checkPositivityDomainFuel (fuel + 1) dom groups activeAddrs).run
        methods initial = .ok () final := by
  unfold checkPositivityDomainFuel
  simp only [hroot, hmentions, Bool.not_true, Bool.false_eq_true, if_false]
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnf dom).run methods) _ initial = _
  unfold EStateM.bind
  rw [hwhnf]
  cases w <;> simp_all [KExpr.collectSpine, KExpr.collectSpine.go]

/-- The direct branch of a successful production positivity traversal
establishes the complete Ix-side valid-recursive-application invariant, with
no inductive oracle premise. -/
theorem checkPositivityDomainFuel_direct_valid
    {fuel : Nat} {dom w : KExpr m}
    {groups : Array (PositivityGroup m)} {activeAddrs : Array Address}
    {methods : Methods m} {initial afterWhnf final : TcState m}
    {rootGroup : PositivityGroup m} {id : KId m}
    {us : Array (KUniv m)} {info : ExprInfo m}
    {args : Array (KExpr m)}
    (hroot : groups[0]? = some rootGroup)
    (hmentions : exprMentionsAnyAddr dom rootGroup.addrs = true)
    (hwhnf : (whnf dom).run methods initial = .ok w afterWhnf)
    (hspine : w.collectSpine = (.const id us info, args))
    (hactive : rootGroup.addrs.contains id.addr = true)
    (hrun :
      (checkPositivityDomainFuel (fuel + 1) dom groups activeAddrs).run
        methods initial = .ok () final) :
    ValidPositiveRecursiveApplication id us args groups rootGroup.addrs methods
      afterWhnf final :=
  checkPositiveRecursiveApplication_valid
    (checkPositivityDomainFuel_direct hroot hmentions hwhnf hspine hactive hrun)

/-- The inactive constant-head branch is exactly the named nested-family
production action, starting from WHNF's post-state.  This is the recursion
boundary used by the nested constructor trace. -/
theorem checkPositivityDomainFuel_nested
    {fuel : Nat} {dom w : KExpr m}
    {groups : Array (PositivityGroup m)} {activeAddrs : Array Address}
    {methods : Methods m} {initial afterWhnf final : TcState m}
    {rootGroup : PositivityGroup m} {id : KId m}
    {us : Array (KUniv m)} {info : ExprInfo m}
    {args : Array (KExpr m)}
    (hroot : groups[0]? = some rootGroup)
    (hmentions : exprMentionsAnyAddr dom rootGroup.addrs = true)
    (hwhnf : (whnf dom).run methods initial = .ok w afterWhnf)
    (hspine : w.collectSpine = (.const id us info, args))
    (hinactive : rootGroup.addrs.contains id.addr = false)
    (hrun :
      (checkPositivityDomainFuel (fuel + 1) dom groups activeAddrs).run
        methods initial = .ok () final) :
    (checkNestedPositivityApplicationFuel fuel id us args groups
      rootGroup.addrs activeAddrs).run methods afterWhnf = .ok () final := by
  unfold checkPositivityDomainFuel at hrun
  simp only [hroot, hmentions, Bool.not_true, Bool.false_eq_true, if_false]
    at hrun
  rw [ReaderT.run_bind] at hrun
  change EStateM.bind ((whnf dom).run methods) _ initial = _ at hrun
  unfold EStateM.bind at hrun
  rw [hwhnf] at hrun
  cases w <;> simp_all [KExpr.collectSpine, KExpr.collectSpine.go]

/-- A successful forall branch exposes the exact opened body and recursive
production traversal.  The final state is the recursive post-state with only
the temporary local-context suffix removed; all other checker effects are
retained. -/
theorem checkPositivityDomainFuel_forall_success
    {fuel : Nat} {dom innerDom innerBody : KExpr m}
    {name : m.F Name} {bi : m.F Lean.BinderInfo} {info : ExprInfo m}
    {groups : Array (PositivityGroup m)} {activeAddrs : Array Address}
    {methods : Methods m} {initial afterWhnf final : TcState m}
    {rootGroup : PositivityGroup m}
    (hroot : groups[0]? = some rootGroup)
    (hmentions : exprMentionsAnyAddr dom rootGroup.addrs = true)
    (hwhnf : (whnf dom).run methods initial =
      .ok (.all name bi innerDom innerBody info) afterWhnf)
    (hnegative : exprMentionsAnyAddr innerDom rootGroup.addrs = false)
    (hrun :
      (checkPositivityDomainFuel (fuel + 1) dom groups activeAddrs).run
        methods initial = .ok () final) :
    ∃ innerOpen fv afterOpen afterRecursive,
      TcM.openBinderAnon innerDom innerBody afterWhnf =
          .ok (innerOpen, fv) afterOpen ∧
        (checkPositivityDomainFuel fuel innerOpen groups activeAddrs).run
            methods afterOpen = .ok () afterRecursive ∧
        final = { afterRecursive with
          lctx := afterRecursive.lctx.truncate afterWhnf.lctx.size } := by
  unfold checkPositivityDomainFuel at hrun
  simp only [hroot, hmentions, Bool.not_true, Bool.false_eq_true, if_false]
    at hrun
  rw [ReaderT.run_bind] at hrun
  change EStateM.bind ((whnf dom).run methods) _ initial = _ at hrun
  unfold EStateM.bind at hrun
  rw [hwhnf] at hrun
  simp only [hnegative, Bool.false_eq_true, if_false] at hrun
  rw [ReaderT.run_bind] at hrun
  change EStateM.bind (get : TcM m (TcState m)) _ afterWhnf = _ at hrun
  unfold EStateM.bind at hrun
  rw [show (get : TcM m (TcState m)) afterWhnf =
    .ok afterWhnf afterWhnf from rfl] at hrun
  simp only at hrun
  rw [ReaderT.run_bind, ReaderT.run_monadLift] at hrun
  change EStateM.bind (TcM.openBinderAnon innerDom innerBody) _ afterWhnf = _
    at hrun
  unfold EStateM.bind at hrun
  cases hopen : TcM.openBinderAnon innerDom innerBody afterWhnf with
  | error _ _ =>
      rw [hopen] at hrun
      contradiction
  | ok opened afterOpen =>
      rcases opened with ⟨innerOpen, fv⟩
      rw [hopen] at hrun
      simp only at hrun
      change (withLctxRestoration afterWhnf.lctx.size
          (checkPositivityDomainFuel fuel innerOpen groups activeAddrs)).run
            methods afterOpen = .ok () final at hrun
      rcases withLctxRestoration_success _ _ _ _ _ hrun with
        ⟨afterRecursive, hrecursive, hfinal⟩
      exact ⟨innerOpen, fv, afterOpen, afterRecursive, rfl, hrecursive, hfinal⟩

/-- A root-family occurrence in a forall domain is rejected immediately at
the post-WHNF state.  No binder is opened and no recursive traversal is
started on this negative-position branch. -/
theorem checkPositivityDomainFuel_forall_negative
    {fuel : Nat} {dom innerDom innerBody : KExpr m}
    {name : m.F Name} {bi : m.F Lean.BinderInfo} {info : ExprInfo m}
    {groups : Array (PositivityGroup m)} {activeAddrs : Array Address}
    {methods : Methods m} {initial afterWhnf : TcState m}
    {rootGroup : PositivityGroup m}
    (hroot : groups[0]? = some rootGroup)
    (hmentions : exprMentionsAnyAddr dom rootGroup.addrs = true)
    (hwhnf : (whnf dom).run methods initial =
      .ok (.all name bi innerDom innerBody info) afterWhnf)
    (hnegative : exprMentionsAnyAddr innerDom rootGroup.addrs = true) :
    (checkPositivityDomainFuel (fuel + 1) dom groups activeAddrs).run
        methods initial =
      .error (.other "strict positivity violation") afterWhnf := by
  unfold checkPositivityDomainFuel
  simp only [hroot, hmentions, Bool.not_true, Bool.false_eq_true, if_false]
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnf dom).run methods) _ initial = _
  unfold EStateM.bind
  rw [hwhnf]
  simp only [hnegative, if_true, throw]
  rfl

end RecM
end Ix.Tc
