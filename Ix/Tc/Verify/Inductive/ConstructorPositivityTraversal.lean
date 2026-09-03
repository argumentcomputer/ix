import Ix.Tc.Verify.Inductive.RecursivePositivityTraversal

/-!
# Complete constructor-positivity traversal

`PositivityDomainTrace` starts after production has already opened the shared
parameter prefix and selected a constructor field.  E2c also needs evidence
that those field calls are the ones reached by the enclosing
`checkPositivity` execution.  This module retains that missing outer spine:
parameter opening, source-ordered field traversal, and final local-context
restoration.
-/

namespace Ix.Tc

/-- Exact successful execution of the production parameter-opening loop.
The `short` case records the deliberately permissive result used so A1/A2 can
report malformed constructor telescopes at their more precise checks. -/
inductive PositivityParameterTrace (methods : Methods m) :
    Nat → KExpr m → Array (KExpr m) → TcState m →
      Option (KExpr m × Array (KExpr m)) → TcState m → Prop
  | done {ty : KExpr m} {paramFVars : Array (KExpr m)}
      {state : TcState m} :
      PositivityParameterTrace methods 0 ty paramFVars state
        (some (ty, paramFVars)) state
  | short {remaining : Nat} {ty w : KExpr m}
      {paramFVars : Array (KExpr m)} {initial afterWhnf : TcState m}
      (whnf : (RecM.whnf ty).run methods initial = .ok w afterWhnf)
      (notForall : PositivityTerminalForm w) :
      PositivityParameterTrace methods (remaining + 1) ty paramFVars initial
        none afterWhnf
  | forall {remaining : Nat} {ty : KExpr m}
      {name : m.F Name} {bi : m.F Lean.BinderInfo}
      {domain body opened fv : KExpr m} {info : ExprInfo m}
      {fvId : FVarId} {paramFVars : Array (KExpr m)}
      {initial afterWhnf afterOpen final : TcState m}
      (whnf : (RecM.whnf ty).run methods initial =
        .ok (.all name bi domain body info) afterWhnf)
      (opening : TcM.openBinderAnonWithFV domain body afterWhnf =
        .ok (opened, fv, fvId) afterOpen)
      (tail : PositivityParameterTrace methods remaining opened
        (paramFVars.push fv) afterOpen result final) :
      PositivityParameterTrace methods (remaining + 1) ty paramFVars initial
        result final

namespace PositivityParameterTrace

/-- Erase a retained parameter-prefix trace back to the exact production
execution.  This lets a concrete successful `some` outcome exclude the
permissive short-telescope trace by determinism. -/
theorem run
    (trace : PositivityParameterTrace methods remaining ty paramFVars initial
      result final) :
    (RecM.openPositivityParameters ty remaining paramFVars).run methods
      initial = .ok result final := by
  induction trace with
  | done => rfl
  | @short remaining ty w paramFVars initial afterWhnf whnf notForall =>
      simp only [RecM.openPositivityParameters, ReaderT.run_bind]
      change EStateM.bind ((RecM.whnf _).run methods) _ _ = _
      unfold EStateM.bind
      rw [whnf]
      cases w <;> simp_all [PositivityTerminalForm] <;> rfl
  | @«forall» remaining ty name bi domain body opened fv info fvId
      paramFVars initial afterWhnf afterOpen final result whnf opening tail ih =>
      simp only [RecM.openPositivityParameters, ReaderT.run_bind]
      change EStateM.bind ((RecM.whnf _).run methods) _ _ = _
      unfold EStateM.bind
      rw [whnf]
      simp only
      rw [ReaderT.run_bind]
      change EStateM.bind (TcM.openBinderAnonWithFV _ _) _ _ = _
      unfold EStateM.bind
      rw [opening]
      exact ih

end PositivityParameterTrace

/-- Exact successful execution of one production field step. -/
inductive ConstructorPositivityFieldStepTrace
    (groups : Array (PositivityGroup m)) (blockAddrs : Array Address)
    (methods : Methods m) (ty : KExpr m) :
    RecM.BoundedStep (KExpr m) Unit → TcState m → TcState m → Prop
  | terminal {w : KExpr m} {initial afterWhnf : TcState m}
      (whnf : (RecM.whnf ty).run methods initial = .ok w afterWhnf)
      (notForall : PositivityTerminalForm w) :
      ConstructorPositivityFieldStepTrace groups blockAddrs methods ty
        (.done ()) initial afterWhnf
  | field {name : m.F Name} {bi : m.F Lean.BinderInfo}
      {domain body opened : KExpr m} {info : ExprInfo m} {fvId : FVarId}
      {initial afterWhnf afterDomain afterOpen : TcState m}
      (whnf : (RecM.whnf ty).run methods initial =
        .ok (.all name bi domain body info) afterWhnf)
      (domainTrace : PositivityDomainTrace groups blockAddrs methods
        maxWhnfFuel.toNat domain afterWhnf afterDomain)
      (opening : TcM.openBinderAnon domain body afterDomain =
        .ok (opened, fvId) afterOpen) :
      ConstructorPositivityFieldStepTrace groups blockAddrs methods ty
        (.next opened) initial afterOpen

/-- Exact successful execution of the bounded, source-ordered field loop.
Each `field` node contains the already exhaustive domain trace, so no callback
or branch oracle is hidden at this layer. -/
inductive ConstructorPositivityFieldsTrace
    (groups : Array (PositivityGroup m)) (blockAddrs : Array Address)
    (methods : Methods m) :
    Nat → KExpr m → TcState m → TcState m → Prop
  | terminal {fuel : Nat} {ty w : KExpr m}
      {initial afterWhnf : TcState m}
      (whnf : (RecM.whnf ty).run methods initial = .ok w afterWhnf)
      (notForall : PositivityTerminalForm w) :
      ConstructorPositivityFieldsTrace groups blockAddrs methods (fuel + 1)
        ty initial afterWhnf
  | field {fuel : Nat} {ty : KExpr m}
      {name : m.F Name} {bi : m.F Lean.BinderInfo}
      {domain body opened : KExpr m} {info : ExprInfo m} {fvId : FVarId}
      {initial afterWhnf afterDomain afterOpen final : TcState m}
      (whnf : (RecM.whnf ty).run methods initial =
        .ok (.all name bi domain body info) afterWhnf)
      (domainTrace : PositivityDomainTrace groups blockAddrs methods
        maxWhnfFuel.toNat domain afterWhnf afterDomain)
      (opening : TcM.openBinderAnon domain body afterDomain =
        .ok (opened, fvId) afterOpen)
      (tail : ConstructorPositivityFieldsTrace groups blockAddrs methods fuel
        opened afterOpen final) :
      ConstructorPositivityFieldsTrace groups blockAddrs methods (fuel + 1)
        ty initial final

/-- Successful execution of `checkPositivityCore`.  The short branch stops
after parameter opening; the full branch retains the exact root group and
complete field loop. -/
inductive ConstructorPositivityCoreTrace
    (ctorTy : KExpr m) (nParams : Nat) (blockAddrs : Array Address)
    (methods : Methods m) : TcState m → TcState m → Prop
  | short {initial final : TcState m}
      (parameters : PositivityParameterTrace methods nParams ctorTy
        (Array.mkEmpty nParams) initial none final) :
      ConstructorPositivityCoreTrace ctorTy nParams blockAddrs methods initial
        final
  | fields {ty : KExpr m} {paramFVars : Array (KExpr m)}
      {initial afterParameters final : TcState m}
      (parameters : PositivityParameterTrace methods nParams ctorTy
        (Array.mkEmpty nParams) initial (some (ty, paramFVars))
          afterParameters)
      (fields : ConstructorPositivityFieldsTrace
        #[{ addrs := blockAddrs, params := paramFVars, concreteUs := none }]
        blockAddrs methods maxWhnfFuel.toNat ty afterParameters final) :
      ConstructorPositivityCoreTrace ctorTy nParams blockAddrs methods initial
        final

/-- Complete successful production `checkPositivity` execution.  All state
effects from WHNF, occurrence checks, and interning are retained; only the
temporary local-context suffix is removed at the public boundary. -/
inductive ConstructorPositivityTrace
    (ctorTy : KExpr m) (nParams : Nat) (blockAddrs : Array Address)
    (methods : Methods m) : TcState m → TcState m → Prop
  | success {initial afterCore final : TcState m}
      (core : ConstructorPositivityCoreTrace ctorTy nParams blockAddrs methods
        initial afterCore)
      (restored : final = { afterCore with
        lctx := afterCore.lctx.truncate initial.lctx.size }) :
      ConstructorPositivityTrace ctorTy nParams blockAddrs methods initial final

namespace RecM

/-- Successful parameter opening is classified exhaustively, including the
short-telescope path. -/
theorem openPositivityParameters_success (methods : Methods m) :
    ∀ {remaining : Nat} {ty : KExpr m}
        {paramFVars : Array (KExpr m)} {initial final : TcState m}
        {result : Option (KExpr m × Array (KExpr m))},
      (openPositivityParameters ty remaining paramFVars).run methods initial =
          .ok result final →
      PositivityParameterTrace methods remaining ty paramFVars initial result
        final
  | 0, ty, paramFVars, initial, final, result, hrun => by
      simp only [openPositivityParameters, ReaderT.run_pure, pure] at hrun
      cases hrun
      exact .done
  | remaining + 1, ty, paramFVars, initial, final, result, hrun => by
      unfold openPositivityParameters at hrun
      rw [ReaderT.run_bind] at hrun
      change EStateM.bind ((whnf ty).run methods) _ initial = _ at hrun
      unfold EStateM.bind at hrun
      cases hwhnf : (whnf ty).run methods initial with
      | error err afterWhnf =>
          rw [hwhnf] at hrun
          contradiction
      | ok w afterWhnf =>
          rw [hwhnf] at hrun
          cases w with
          | all name bi domain body info =>
              simp only at hrun
              rw [ReaderT.run_bind] at hrun
              change EStateM.bind (TcM.openBinderAnonWithFV domain body) _
                afterWhnf = _ at hrun
              unfold EStateM.bind at hrun
              cases hopen : TcM.openBinderAnonWithFV domain body afterWhnf with
              | error err afterOpen =>
                  rw [hopen] at hrun
                  contradiction
              | ok value afterOpen =>
                  rcases value with ⟨opened, fv, fvId⟩
                  rw [hopen] at hrun
                  exact .forall hwhnf hopen
                    (openPositivityParameters_success methods hrun)
          | var | fvar | sort | const | app | lam | letE | prj | nat | str =>
              simp only at hrun
              simp only [ReaderT.run_pure, pure] at hrun
              cases hrun
              exact .short hwhnf trivial

/-- Every successful production field step exposes either the terminal WHNF
or the complete field-domain and opening transitions. -/
theorem checkPositivityFieldStep_success (methods : Methods m)
    {groups : Array (PositivityGroup m)} {blockAddrs : Array Address}
    {ty : KExpr m} {action : BoundedStep (KExpr m) Unit}
    {initial final : TcState m}
    (hrun : (checkPositivityFieldStep groups blockAddrs ty).run methods
      initial = .ok action final) :
    ConstructorPositivityFieldStepTrace groups blockAddrs methods ty action
      initial final := by
  unfold checkPositivityFieldStep at hrun
  rw [ReaderT.run_bind] at hrun
  change EStateM.bind ((whnf ty).run methods) _ initial = _ at hrun
  unfold EStateM.bind at hrun
  cases hwhnf : (whnf ty).run methods initial with
  | error err afterWhnf =>
      rw [hwhnf] at hrun
      contradiction
  | ok w afterWhnf =>
      rw [hwhnf] at hrun
      cases w with
      | all name bi domain body info =>
          simp only at hrun
          rw [ReaderT.run_bind] at hrun
          change EStateM.bind
            ((checkPositivityDomain domain groups blockAddrs).run methods) _
              afterWhnf = _ at hrun
          unfold EStateM.bind at hrun
          cases hdomain :
              (checkPositivityDomain domain groups blockAddrs).run methods
                afterWhnf with
          | error err afterDomain =>
              rw [hdomain] at hrun
              contradiction
          | ok value afterDomain =>
              cases value
              rw [hdomain] at hrun
              rw [ReaderT.run_bind] at hrun
              change EStateM.bind (TcM.openBinderAnon domain body) _
                afterDomain = _ at hrun
              unfold EStateM.bind at hrun
              cases hopen : TcM.openBinderAnon domain body afterDomain with
              | error err afterOpen =>
                  rw [hopen] at hrun
                  contradiction
              | ok value afterOpen =>
                  rcases value with ⟨opened, fvId⟩
                  rw [hopen] at hrun
                  simp only [ReaderT.run_pure, pure] at hrun
                  cases hrun
                  refine .field hwhnf ?_ hopen
                  unfold checkPositivityDomain at hdomain
                  exact checkPositivityDomainFuel_success methods hdomain
      | var | fvar | sort | const | app | lam | letE | prj | nat | str =>
          simp only at hrun
          simp only [ReaderT.run_pure, pure] at hrun
          cases hrun
          exact .terminal hwhnf trivial

/-- Every successful bounded field traversal yields its complete
source-ordered execution tree. -/
theorem checkPositivityFields_success (methods : Methods m) :
    ∀ {fuel : Nat} {groups : Array (PositivityGroup m)}
        {blockAddrs : Array Address} {ty : KExpr m}
        {initial final : TcState m},
      (runBounded (checkPositivityFieldStep groups blockAddrs) fuel ty).run
          methods initial = .ok () final →
      ConstructorPositivityFieldsTrace groups blockAddrs methods fuel ty
        initial final
  | 0, groups, blockAddrs, ty, initial, final, hrun => by
      simp only [runBounded, throw, ReaderT.run] at hrun
      contradiction
  | fuel + 1, groups, blockAddrs, ty, initial, final, hrun => by
      unfold runBounded at hrun
      rw [ReaderT.run_bind] at hrun
      change EStateM.bind
        ((checkPositivityFieldStep groups blockAddrs ty).run methods) _
          initial = _ at hrun
      unfold EStateM.bind at hrun
      cases hstep :
          (checkPositivityFieldStep groups blockAddrs ty).run methods initial with
      | error err afterStep =>
          rw [hstep] at hrun
          contradiction
      | ok action afterStep =>
          rw [hstep] at hrun
          have trace := checkPositivityFieldStep_success methods hstep
          cases trace with
          | terminal hwhnf hnotForall =>
              simp only [ReaderT.run_pure, pure] at hrun
              cases hrun
              exact .terminal hwhnf hnotForall
          | field hwhnf hdomain hopen =>
              exact .field hwhnf hdomain hopen
                (checkPositivityFields_success methods hrun)

/-- Every successful protected positivity body yields the complete parameter
and field execution tree. -/
theorem checkPositivityCore_success (methods : Methods m)
    {ctorTy : KExpr m} {nParams : Nat} {blockAddrs : Array Address}
    {initial final : TcState m}
    (hrun : (checkPositivityCore ctorTy nParams blockAddrs).run methods
      initial = .ok () final) :
    ConstructorPositivityCoreTrace ctorTy nParams blockAddrs methods initial
      final := by
  unfold checkPositivityCore at hrun
  rw [ReaderT.run_bind] at hrun
  change EStateM.bind
    ((openPositivityParameters ctorTy nParams (Array.mkEmpty nParams)).run
      methods) _ initial = _ at hrun
  unfold EStateM.bind at hrun
  cases hparameters :
      (openPositivityParameters ctorTy nParams (Array.mkEmpty nParams)).run
        methods initial with
  | error err afterParameters =>
      rw [hparameters] at hrun
      contradiction
  | ok result afterParameters =>
      rw [hparameters] at hrun
      have parameterTrace := openPositivityParameters_success methods hparameters
      cases result with
      | none =>
          simp only [ReaderT.run_pure, pure] at hrun
          cases hrun
          exact .short parameterTrace
      | some payload =>
          rcases payload with ⟨ty, paramFVars⟩
          exact .fields parameterTrace
            (checkPositivityFields_success methods hrun)

/-- At a fixed initial state the public reducer is definitionally the generic
scope-restoration wrapper around its named protected body. -/
private theorem checkPositivity_run_withLctxRestoration
    (ctorTy : KExpr m) (nParams : Nat) (blockAddrs : Array Address)
    (methods : Methods m) (initial : TcState m) :
    (checkPositivity ctorTy nParams blockAddrs).run methods initial =
      (withLctxRestoration initial.lctx.size
        (checkPositivityCore ctorTy nParams blockAddrs)).run methods initial := by
  rfl

/-- Every successful public constructor-positivity run yields the complete
outer trace, including its exact restoration boundary. -/
theorem checkPositivity_success (methods : Methods m)
    {ctorTy : KExpr m} {nParams : Nat} {blockAddrs : Array Address}
    {initial final : TcState m}
    (hrun : (checkPositivity ctorTy nParams blockAddrs).run methods initial =
      .ok () final) :
    ConstructorPositivityTrace ctorTy nParams blockAddrs methods initial
      final := by
  rw [checkPositivity_run_withLctxRestoration] at hrun
  obtain ⟨afterCore, hcore, hrestored⟩ :=
    withLctxRestoration_success initial.lctx.size
      (checkPositivityCore ctorTy nParams blockAddrs) methods initial final hrun
  exact .success (checkPositivityCore_success methods hcore) hrestored

end RecM
end Ix.Tc
