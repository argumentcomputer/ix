import Ix.Tc.Verify.Inductive.PositivityTraversal
import Ix.Tc.Verify.Inductive.SpecializationIdentity

/-!
# Nested-family positivity traversal

The inactive constant-head branch of production positivity validates an
external inductive application, then recursively validates the constructor
fields of that external family under an augmented positivity context.  This
module exposes that execution without replacing any production guard with an
oracle premise.

The first boundary is the lazy constant lookup.  A successful run identifies
the exact loaded inductive header and continues from the real post-lookup
checker state with the header's concrete arities, block, and constructor list.
-/

namespace Ix.Tc

/-- Header information read from an external family reached by nested
positivity traversal. -/
def KConst.NestedPositiveHeader (concrete : KConst m)
    (nParams nIndices levels : Nat) (block : KId m)
    (ctors : Array (KId m)) : Prop :=
  match concrete with
  | .indc (params := params) (indices := indices) (lvls := lvls)
      (block := loadedBlock) (ctors := loadedCtors) .. =>
      params.toNat = nParams ∧ indices.toNat = nIndices ∧
        lvls.toNat = levels ∧ loadedBlock = block ∧ loadedCtors = ctors
  | _ => False

/-- The concrete lookup reached by nested traversal is a constructor with the
exact type passed to recursive field validation. -/
def KConst.NestedConstructorHeader (concrete : KConst m)
    (ctorTy : KExpr m) : Prop :=
  match concrete with
  | .ctor (ty := loadedTy) .. => loadedTy = ctorTy
  | _ => False

/-- Exact successful-branch trace of the nested-family header lookup. -/
def NestedPositivityApplicationTrace
    (fuel : Nat) (id : KId m) (us : Array (KUniv m))
    (args : Array (KExpr m)) (groups : Array (PositivityGroup m))
    (rootAddrs activeAddrs : Array Address) (methods : Methods m)
    (initial final : TcState m) : Prop :=
  ∃ concrete nParams nIndices levels block ctors afterLookup,
    TcM.getConst id initial = .ok concrete afterLookup ∧
      concrete.NestedPositiveHeader nParams nIndices levels block ctors ∧
      (RecM.checkNestedPositivityApplicationResolvedFuel fuel id us args
        groups rootAddrs activeAddrs nParams nIndices levels block ctors).run
          methods afterLookup = .ok () final

/-- Successful execution after header resolution: both application arities
are exact and the checked specialization/constructor continuation succeeds
from the same checker state. -/
def NestedPositivityResolvedTrace
    (fuel : Nat) (id : KId m) (us : Array (KUniv m))
    (args : Array (KExpr m)) (groups : Array (PositivityGroup m))
    (rootAddrs activeAddrs : Array Address) (nParams nIndices levels : Nat)
    (block : KId m) (ctors : Array (KId m)) (methods : Methods m)
    (initial final : TcState m) : Prop :=
  args.size = nParams + nIndices ∧
    us.size = levels ∧
    (RecM.checkNestedPositivityApplicationCheckedFuel fuel id us args groups
      rootAddrs activeAddrs nParams block ctors).run methods initial =
        .ok () final

/-- Exhaustive successful execution of the checked nested-family branch.
An existing exact specialization closes at the current state after its index
guard; a fresh specialization records the parameter/index guards and enters
the stateful block-discovery/constructor continuation. -/
inductive NestedPositivityCheckedTrace
    (fuel : Nat) (id : KId m) (us : Array (KUniv m))
    (args : Array (KExpr m)) (groups : Array (PositivityGroup m))
    (rootAddrs activeAddrs : Array Address) (nParams : Nat)
    (block : KId m) (ctors : Array (KId m)) (methods : Methods m) :
    TcState m → TcState m → Prop
  | existing (group : PositivityGroup m) (state : TcState m)
      (selected : RecM.findNestedPositivityGroup? groups id.addr us args
        nParams = some group)
      (indicesIndependent :
        RecM.positiveIndicesIndependent args nParams rootAddrs = true) :
      NestedPositivityCheckedTrace fuel id us args groups rootAddrs activeAddrs
        nParams block ctors methods state state
  | fresh {initial final : TcState m}
      (absent : RecM.findNestedPositivityGroup? groups id.addr us args
        nParams = none)
      (parameterMention :
        RecM.nestedParametersMentionRoot args nParams rootAddrs = true)
      (indicesIndependent :
        RecM.positiveIndicesIndependent args nParams rootAddrs = true)
      (continuation :
        (RecM.checkFreshNestedPositivityApplicationFuel fuel us args groups
          activeAddrs nParams block ctors).run methods initial = .ok () final) :
      NestedPositivityCheckedTrace fuel id us args groups rootAddrs activeAddrs
        nParams block ctors methods initial final

/-- Exact successful execution of one nested constructor lookup and its field
validator. -/
def NestedConstructorTrace
    (fuel : Nat) (ctorId : KId m) (nParams : Nat)
    (paramArgs : Array (KExpr m)) (us : Array (KUniv m))
    (groups : Array (PositivityGroup m)) (activeAddrs : Array Address)
    (methods : Methods m) (initial final : TcState m) : Prop :=
  ∃ concrete ctorTy afterLookup,
    TcM.getConst ctorId initial = .ok concrete afterLookup ∧
      concrete.NestedConstructorHeader ctorTy ∧
      (RecM.checkNestedCtorFieldsFuel fuel ctorTy nParams paramArgs us groups
        activeAddrs).run methods afterLookup = .ok () final

/-- Source-ordered state-threaded trace for the constructor array of one
fresh nested specialization. -/
inductive NestedConstructorListTrace
    (fuel : Nat) (nParams : Nat) (paramArgs : Array (KExpr m))
    (us : Array (KUniv m)) (groups : Array (PositivityGroup m))
    (activeAddrs : Array Address) (methods : Methods m) :
    List (KId m) → TcState m → TcState m → Prop
  | nil (state : TcState m) :
      NestedConstructorListTrace fuel nParams paramArgs us groups activeAddrs
        methods [] state state
  | cons {ctorId : KId m} {ctors : List (KId m)}
      {initial afterCtor final : TcState m}
      (head : NestedConstructorTrace fuel ctorId nParams paramArgs us groups
        activeAddrs methods initial afterCtor)
      (tail : NestedConstructorListTrace fuel nParams paramArgs us groups
        activeAddrs methods ctors afterCtor final) :
      NestedConstructorListTrace fuel nParams paramArgs us groups activeAddrs
        methods (ctorId :: ctors) initial final

/-- Complete successful execution of the fresh-specialization continuation:
the external mutual block is discovered, the exact augmented positivity
context is constructed, and every stored constructor is traversed. -/
def FreshNestedPositivityTrace
    (fuel : Nat) (us : Array (KUniv m)) (args : Array (KExpr m))
    (groups : Array (PositivityGroup m)) (activeAddrs : Array Address)
    (nParams : Nat) (block : KId m) (ctors : Array (KId m))
    (methods : Methods m) (initial final : TcState m) : Prop :=
  ∃ extBlockInductives afterDiscovery,
    (RecM.discoverBlockInductives block).run methods initial =
        .ok extBlockInductives afterDiscovery ∧
      NestedConstructorListTrace fuel nParams
        (args.extract 0 (min nParams args.size)) us
        (groups.push
          { addrs := extBlockInductives.map (·.addr)
            params := args.extract 0 (min nParams args.size)
            concreteUs := some us })
        (activeAddrs ++ extBlockInductives.map (·.addr)) methods ctors.toList
        afterDiscovery final

/-- Exact WHNF executions used to strip the external family's complete
parameter prefix.  There is deliberately no short-telescope constructor:
production now rejects a non-forall reached before every declared parameter
has been removed. -/
inductive NestedParameterStripTrace (methods : Methods m) :
    KExpr m → Nat → KExpr m → TcState m → TcState m → Prop
  | done (ty : KExpr m) (state : TcState m) :
      NestedParameterStripTrace methods ty 0 ty state state
  | forall {ty : KExpr m} {remaining : Nat}
      {name : m.F Name} {bi : m.F Lean.BinderInfo}
      {dom body : KExpr m} {info : ExprInfo m}
      {initial afterWhnf final : TcState m}
      (whnfRun : (RecM.whnf ty).run methods initial =
        .ok (.all name bi dom body info) afterWhnf)
      (tail : NestedParameterStripTrace methods body remaining result
        afterWhnf final) :
      NestedParameterStripTrace methods ty (remaining + 1) result initial final

/-- Exact successful execution of the recursive field loop after nested-family
parameter substitution.  A terminal WHNF closes immediately.  A forall first
validates its field domain, then opens the dependent body and recursively
traverses it while removing only the temporary local-context suffix. -/
inductive NestedFieldLoopTrace
    (groups : Array (PositivityGroup m)) (activeAddrs : Array Address)
    (methods : Methods m) :
    Nat → KExpr m → TcState m → TcState m → Prop
  | terminal {fuel : Nat} {ty w : KExpr m}
      {initial afterWhnf : TcState m}
      (whnfRun : (RecM.whnf ty).run methods initial = .ok w afterWhnf)
      (notForall : match w with | .all .. => False | _ => True) :
      NestedFieldLoopTrace groups activeAddrs methods (fuel + 1) ty initial
        afterWhnf
  | forall {fuel : Nat} {ty : KExpr m}
      {name : m.F Name} {bi : m.F Lean.BinderInfo}
      {dom body openBody : KExpr m} {info : ExprInfo m}
      {fv : FVarId}
      {initial afterWhnf afterDomain afterOpen afterRecursive final : TcState m}
      (whnfRun : (RecM.whnf ty).run methods initial =
        .ok (.all name bi dom body info) afterWhnf)
      (domainRun :
        (RecM.checkPositivityDomainFuel fuel dom groups activeAddrs).run methods
          afterWhnf = .ok () afterDomain)
      (opening : TcM.openBinderAnon dom body afterDomain =
        .ok (openBody, fv) afterOpen)
      (tail : NestedFieldLoopTrace groups activeAddrs methods fuel openBody
        afterOpen afterRecursive)
      (restored : final = { afterRecursive with
        lctx := afterRecursive.lctx.truncate afterDomain.lctx.size }) :
      NestedFieldLoopTrace groups activeAddrs methods (fuel + 1) ty initial final

/-- Complete successful execution of one nested constructor's field
transformer.  It records universe instantiation, every declared parameter
binder, simultaneous reversed substitution, and entry into the recursive
field loop.  Successful execution cannot bypass this path via a malformed
short telescope. -/
inductive NestedCtorFieldsTrace
    (fuel : Nat) (ctorTy : KExpr m) (nParams : Nat)
    (paramArgs : Array (KExpr m)) (us : Array (KUniv m))
    (groups : Array (PositivityGroup m)) (activeAddrs : Array Address)
    (methods : Methods m) : TcState m → TcState m → Prop
  | complete {instantiated stripped substituted : KExpr m}
      {initial afterInstantiation afterStripping afterSubstitution final :
        TcState m}
      (instantiation : TcM.instantiateUnivParams ctorTy us initial =
        .ok instantiated afterInstantiation)
      (stripping : (RecM.stripNestedCtorParameters instantiated nParams).run
        methods afterInstantiation = .ok stripped afterStripping)
      (stripTrace : NestedParameterStripTrace methods instantiated nParams
        stripped afterInstantiation afterStripping)
      (substitution :
        TcM.runIntern (simulSubst stripped paramArgs.reverse 0)
          afterStripping = .ok substituted afterSubstitution)
      (fieldLoop :
        (RecM.checkNestedCtorFieldsLoopFuel fuel substituted groups
          activeAddrs).run methods afterSubstitution = .ok () final)
      (fieldTrace : NestedFieldLoopTrace groups activeAddrs methods fuel
        substituted afterSubstitution final) :
      NestedCtorFieldsTrace fuel ctorTy nParams paramArgs us groups activeAddrs
        methods initial final

/-- Fully expanded successful trace of one constructor action.  The explicit
successor equation records that a nonempty constructor traversal cannot hide a
fuel-zero field check. -/
def CompleteNestedConstructorTrace
    (fuel : Nat) (ctorId : KId m) (nParams : Nat)
    (paramArgs : Array (KExpr m)) (us : Array (KUniv m))
    (groups : Array (PositivityGroup m)) (activeAddrs : Array Address)
    (methods : Methods m) (initial final : TcState m) : Prop :=
  ∃ innerFuel concrete ctorTy afterLookup,
    fuel = innerFuel + 1 ∧
      TcM.getConst ctorId initial = .ok concrete afterLookup ∧
      concrete.NestedConstructorHeader ctorTy ∧
      NestedCtorFieldsTrace innerFuel ctorTy nParams paramArgs us groups
        activeAddrs methods afterLookup final

/-- Source-ordered constructor traversal with every lookup, instantiation,
parameter stripping, substitution, and recursive field loop expanded. -/
inductive CompleteNestedConstructorListTrace
    (fuel : Nat) (nParams : Nat) (paramArgs : Array (KExpr m))
    (us : Array (KUniv m)) (groups : Array (PositivityGroup m))
    (activeAddrs : Array Address) (methods : Methods m) :
    List (KId m) → TcState m → TcState m → Prop
  | nil (state : TcState m) :
      CompleteNestedConstructorListTrace fuel nParams paramArgs us groups
        activeAddrs methods [] state state
  | cons {ctorId : KId m} {ctors : List (KId m)}
      {initial afterCtor final : TcState m}
      (head : CompleteNestedConstructorTrace fuel ctorId nParams paramArgs us
        groups activeAddrs methods initial afterCtor)
      (tail : CompleteNestedConstructorListTrace fuel nParams paramArgs us
        groups activeAddrs methods ctors afterCtor final) :
      CompleteNestedConstructorListTrace fuel nParams paramArgs us groups
        activeAddrs methods (ctorId :: ctors) initial final

/-- Fully expanded fresh-specialization continuation. -/
def CompleteFreshNestedPositivityTrace
    (fuel : Nat) (us : Array (KUniv m)) (args : Array (KExpr m))
    (groups : Array (PositivityGroup m)) (activeAddrs : Array Address)
    (nParams : Nat) (block : KId m) (ctors : Array (KId m))
    (methods : Methods m) (initial final : TcState m) : Prop :=
  ∃ extBlockInductives afterDiscovery,
    (RecM.discoverBlockInductives block).run methods initial =
        .ok extBlockInductives afterDiscovery ∧
      CompleteNestedConstructorListTrace fuel nParams
        (args.extract 0 (min nParams args.size)) us
        (groups.push
          { addrs := extBlockInductives.map (·.addr)
            params := args.extract 0 (min nParams args.size)
            concreteUs := some us })
        (activeAddrs ++ extBlockInductives.map (·.addr)) methods ctors.toList
        afterDiscovery final

/-- Fully expanded checked nested-family branch. -/
inductive CompleteNestedPositivityCheckedTrace
    (fuel : Nat) (id : KId m) (us : Array (KUniv m))
    (args : Array (KExpr m)) (groups : Array (PositivityGroup m))
    (rootAddrs activeAddrs : Array Address) (nParams : Nat)
    (block : KId m) (ctors : Array (KId m)) (methods : Methods m) :
    TcState m → TcState m → Prop
  | existing (group : PositivityGroup m) (state : TcState m)
      (selected : RecM.findNestedPositivityGroup? groups id.addr us args
        nParams = some group)
      (indicesIndependent :
        RecM.positiveIndicesIndependent args nParams rootAddrs = true) :
      CompleteNestedPositivityCheckedTrace fuel id us args groups rootAddrs
        activeAddrs nParams block ctors methods state state
  | fresh {initial final : TcState m}
      (absent : RecM.findNestedPositivityGroup? groups id.addr us args
        nParams = none)
      (parameterMention :
        RecM.nestedParametersMentionRoot args nParams rootAddrs = true)
      (indicesIndependent :
        RecM.positiveIndicesIndependent args nParams rootAddrs = true)
      (continuation : CompleteFreshNestedPositivityTrace fuel us args groups
        activeAddrs nParams block ctors methods initial final) :
      CompleteNestedPositivityCheckedTrace fuel id us args groups rootAddrs
        activeAddrs nParams block ctors methods initial final

/-- Header-resolved nested traversal with exact arities and a fully expanded
checked continuation. -/
def CompleteNestedPositivityResolvedTrace
    (fuel : Nat) (id : KId m) (us : Array (KUniv m))
    (args : Array (KExpr m)) (groups : Array (PositivityGroup m))
    (rootAddrs activeAddrs : Array Address) (nParams nIndices levels : Nat)
    (block : KId m) (ctors : Array (KId m)) (methods : Methods m)
    (initial final : TcState m) : Prop :=
  args.size = nParams + nIndices ∧
    us.size = levels ∧
    CompleteNestedPositivityCheckedTrace fuel id us args groups rootAddrs
      activeAddrs nParams block ctors methods initial final

/-- Full successful trace from the external-family lookup through every
nested constructor field reached by production. -/
def CompleteNestedPositivityApplicationTrace
    (fuel : Nat) (id : KId m) (us : Array (KUniv m))
    (args : Array (KExpr m)) (groups : Array (PositivityGroup m))
    (rootAddrs activeAddrs : Array Address) (methods : Methods m)
    (initial final : TcState m) : Prop :=
  ∃ concrete nParams nIndices levels block ctors afterLookup,
    TcM.getConst id initial = .ok concrete afterLookup ∧
      concrete.NestedPositiveHeader nParams nIndices levels block ctors ∧
      CompleteNestedPositivityResolvedTrace fuel id us args groups rootAddrs
        activeAddrs nParams nIndices levels block ctors methods afterLookup final

namespace RecM

/-- Expose one concrete checker bind while decomposing source-ordered
constructor traversal. -/
private theorem runTcBind {α β : Type}
    (x : TcM m α) (k : α → TcM m β) (state : TcState m) :
    (x >>= k) state = match x state with
      | .ok value after => k value after
      | .error err after => .error err after := by
  show EStateM.bind x k state = _
  unfold EStateM.bind
  cases x state <;> rfl

/-- Selecting an existing specialization exposes both membership in the
active stack and the exact structural identity shared with flat-block
auxiliary generation. -/
theorem findNestedPositivityGroup?_some
    {groups : Array (PositivityGroup m)} {family : Address}
    {us : Array (KUniv m)} {args : Array (KExpr m)} {nParams : Nat}
    {group : PositivityGroup m}
    (hfind : findNestedPositivityGroup? groups family us args nParams =
      some group) :
    group ∈ groups ∧ group.addrs.contains family = true ∧
      PositivityFlatIdentity group family us args nParams := by
  unfold findNestedPositivityGroup? at hfind
  have hmem := Array.mem_of_find?_eq_some hfind
  have hpredicate := Array.find?_some hfind
  rw [Bool.and_eq_true] at hpredicate
  exact ⟨hmem, hpredicate.1,
    (positivityGroupMatches_eq_true_iff _ _ _ _ _).mp hpredicate.2⟩

/-- The external-family arity guard succeeds exactly for a fully applied
inductive header with the declared universe count. -/
theorem checkNestedPositivityApplicationPreconditions_success_iff
    {us : Array (KUniv m)} {args : Array (KExpr m)}
    {nParams nIndices levels : Nat} :
    checkNestedPositivityApplicationPreconditions us args nParams nIndices
        levels = .ok () ↔
      args.size = nParams + nIndices ∧ us.size = levels := by
  unfold checkNestedPositivityApplicationPreconditions
  by_cases hargs : args.size = nParams + nIndices
  · by_cases hus : us.size = levels
    · simp [hargs, hus]
    · simp [hargs, hus]
  · simp [hargs]

/-- A successful resolved-header run exposes exact arities and enters the
named checked continuation without changing the checker state. -/
theorem checkNestedPositivityApplicationResolvedFuel_success
    {fuel : Nat} {id : KId m} {us : Array (KUniv m)}
    {args : Array (KExpr m)} {groups : Array (PositivityGroup m)}
    {rootAddrs activeAddrs : Array Address} {nParams nIndices levels : Nat}
    {block : KId m} {ctors : Array (KId m)} {methods : Methods m}
    {initial final : TcState m}
    (hrun : (checkNestedPositivityApplicationResolvedFuel fuel id us args
      groups rootAddrs activeAddrs nParams nIndices levels block ctors).run
        methods initial = .ok () final) :
    NestedPositivityResolvedTrace fuel id us args groups rootAddrs activeAddrs
      nParams nIndices levels block ctors methods initial final := by
  unfold checkNestedPositivityApplicationResolvedFuel at hrun
  generalize hpreconditions :
      checkNestedPositivityApplicationPreconditions us args nParams nIndices
        levels = preconditionResult at hrun
  cases preconditionResult with
  | error err =>
      simp only at hrun
      change EStateM.Result.error err initial = .ok () final at hrun
      contradiction
  | ok value =>
      cases value
      have harities :=
        checkNestedPositivityApplicationPreconditions_success_iff.mp
          hpreconditions
      simp only at hrun
      exact ⟨harities.1, harities.2, hrun⟩

/-- The checked continuation's successful executions are exhausted by the
existing-specialization and fresh-specialization cases. -/
theorem checkNestedPositivityApplicationCheckedFuel_success
    {fuel : Nat} {id : KId m} {us : Array (KUniv m)}
    {args : Array (KExpr m)} {groups : Array (PositivityGroup m)}
    {rootAddrs activeAddrs : Array Address} {nParams : Nat}
    {block : KId m} {ctors : Array (KId m)} {methods : Methods m}
    {initial final : TcState m}
    (hrun : (checkNestedPositivityApplicationCheckedFuel fuel id us args
      groups rootAddrs activeAddrs nParams block ctors).run methods initial =
        .ok () final) :
    NestedPositivityCheckedTrace fuel id us args groups rootAddrs activeAddrs
      nParams block ctors methods initial final := by
  unfold checkNestedPositivityApplicationCheckedFuel at hrun
  generalize hselected :
      findNestedPositivityGroup? groups id.addr us args nParams = selected
        at hrun
  cases selected with
  | none =>
      simp only at hrun
      cases hmention : nestedParametersMentionRoot args nParams rootAddrs with
      | false =>
          simp only [hmention, Bool.not_false, if_true] at hrun
          change EStateM.Result.error _ initial = .ok () final at hrun
          contradiction
      | true =>
          simp only [hmention, Bool.not_true] at hrun
          cases hindependent :
              positiveIndicesIndependent args nParams rootAddrs with
          | false =>
              simp only [hindependent, Bool.not_false, if_true] at hrun
              change EStateM.Result.error _ initial = .ok () final at hrun
              contradiction
          | true =>
              simp only [hindependent, Bool.not_true] at hrun
              exact .fresh hselected hmention hindependent hrun
  | some group =>
      simp only at hrun
      cases hindependent : positiveIndicesIndependent args nParams rootAddrs with
      | false =>
          simp only [hindependent, Bool.not_false, if_true] at hrun
          change EStateM.Result.error _ initial = .ok () final at hrun
          contradiction
      | true =>
          simp only [hindependent, Bool.not_true, pure,
            ReaderT.run] at hrun
          cases hrun
          exact .existing group initial hselected hindependent

/-- A successful per-constructor action identifies the exact loaded
constructor type and the recursive field-check execution that consumed it. -/
theorem checkNestedConstructorFuel_success
    {fuel : Nat} {ctorId : KId m} {nParams : Nat}
    {paramArgs : Array (KExpr m)} {us : Array (KUniv m)}
    {groups : Array (PositivityGroup m)} {activeAddrs : Array Address}
    {methods : Methods m} {initial final : TcState m}
    (hrun : (checkNestedConstructorFuel fuel ctorId nParams paramArgs us
      groups activeAddrs).run methods initial = .ok () final) :
    NestedConstructorTrace fuel ctorId nParams paramArgs us groups activeAddrs
      methods initial final := by
  unfold checkNestedConstructorFuel at hrun
  simp only [ReaderT.run_bind, ReaderT.run_monadLift, monadLift_self] at hrun
  change EStateM.bind (TcM.getConst ctorId) _ initial = _ at hrun
  unfold EStateM.bind at hrun
  cases hlookup : TcM.getConst ctorId initial with
  | error err afterLookup =>
      rw [hlookup] at hrun
      contradiction
  | ok concrete afterLookup =>
      rw [hlookup] at hrun
      cases concrete with
      | ctor name levelParams isUnsafe lvls induct cidx params fields ty =>
          simp only at hrun
          exact ⟨.ctor name levelParams isUnsafe lvls induct cidx params fields
              ty,
            ty, afterLookup, hlookup, rfl, hrun⟩
      | defn name levelParams kind safety hints lvls ty value leanAll block =>
          change EStateM.Result.error _ afterLookup = .ok () final at hrun
          contradiction
      | indc name levelParams lvls params indices isUnsafe block memberIdx ty
          ctors leanAll =>
          change EStateM.Result.error _ afterLookup = .ok () final at hrun
          contradiction
      | recr name levelParams k isUnsafe lvls params indices motives minors
          block memberIdx ty rules leanAll =>
          change EStateM.Result.error _ afterLookup = .ok () final at hrun
          contradiction
      | axio name levelParams isUnsafe lvls ty =>
          change EStateM.Result.error _ afterLookup = .ok () final at hrun
          contradiction
      | quot name levelParams kind lvls ty =>
          change EStateM.Result.error _ afterLookup = .ok () final at hrun
          contradiction

/-- List-normalized successful constructor loop. -/
private theorem checkNestedConstructorsList_success
    (fuel : Nat) (nParams : Nat) (paramArgs : Array (KExpr m))
    (us : Array (KUniv m)) (groups : Array (PositivityGroup m))
    (activeAddrs : Array Address) (methods : Methods m) :
    ∀ {ctors : List (KId m)} {initial final : TcState m},
      ((do
        forIn (m := RecM m) ctors () (fun ctorId _ => do
          checkNestedConstructorFuel fuel ctorId nParams paramArgs us groups
            activeAddrs
          pure (.yield ()))
        pure ()).run methods initial = .ok () final) →
      NestedConstructorListTrace fuel nParams paramArgs us groups activeAddrs
        methods ctors initial final
  | [], initial, final, hrun => by
      simp only [List.forIn_nil, ReaderT.run_pure, pure_bind] at hrun
      cases hrun
      exact .nil initial
  | ctorId :: ctors, initial, final, hrun => by
      rw [List.forIn_cons, ReaderT.run_bind] at hrun
      rw [ReaderT.run_bind] at hrun
      rw [bind_assoc] at hrun
      rw [ReaderT.run_bind] at hrun
      rw [bind_assoc] at hrun
      rw [runTcBind] at hrun
      cases hhead :
          (checkNestedConstructorFuel fuel ctorId nParams paramArgs us groups
            activeAddrs).run methods initial with
      | error err afterCtor =>
          rw [hhead] at hrun
          contradiction
      | ok value afterCtor =>
          rw [hhead] at hrun
          cases value
          simp only at hrun
          exact .cons (checkNestedConstructorFuel_success hhead)
            (checkNestedConstructorsList_success fuel nParams paramArgs us
              groups activeAddrs methods hrun)

/-- Every successful production constructor-array traversal records all
concrete constructor lookups and recursive field checks in source order. -/
theorem checkNestedConstructorsFuel_success
    {fuel : Nat} {ctors : Array (KId m)} {nParams : Nat}
    {paramArgs : Array (KExpr m)} {us : Array (KUniv m)}
    {groups : Array (PositivityGroup m)} {activeAddrs : Array Address}
    {methods : Methods m} {initial final : TcState m}
    (hrun : (checkNestedConstructorsFuel fuel ctors nParams paramArgs us
      groups activeAddrs).run methods initial = .ok () final) :
    NestedConstructorListTrace fuel nParams paramArgs us groups activeAddrs
      methods ctors.toList initial final := by
  unfold checkNestedConstructorsFuel at hrun
  rw [← Array.forIn_toList] at hrun
  exact checkNestedConstructorsList_success fuel nParams paramArgs us groups
    activeAddrs methods hrun

/-- A successful fresh-specialization continuation exposes its exact block
discovery result and complete source-ordered constructor traversal. -/
theorem checkFreshNestedPositivityApplicationFuel_success
    {fuel : Nat} {us : Array (KUniv m)} {args : Array (KExpr m)}
    {groups : Array (PositivityGroup m)} {activeAddrs : Array Address}
    {nParams : Nat} {block : KId m} {ctors : Array (KId m)}
    {methods : Methods m} {initial final : TcState m}
    (hrun : (checkFreshNestedPositivityApplicationFuel fuel us args groups
      activeAddrs nParams block ctors).run methods initial = .ok () final) :
    FreshNestedPositivityTrace fuel us args groups activeAddrs nParams block
      ctors methods initial final := by
  unfold checkFreshNestedPositivityApplicationFuel at hrun
  rw [ReaderT.run_bind] at hrun
  change EStateM.bind ((discoverBlockInductives block).run methods) _ initial =
    _ at hrun
  unfold EStateM.bind at hrun
  cases hdiscover : (discoverBlockInductives block).run methods initial with
  | error err afterDiscovery =>
      rw [hdiscover] at hrun
      contradiction
  | ok extBlockInductives afterDiscovery =>
      rw [hdiscover] at hrun
      simp only at hrun
      exact ⟨extBlockInductives, afterDiscovery, hdiscover,
        checkNestedConstructorsFuel_success hrun⟩

/-- Successful parameter stripping records every WHNF step and therefore
certifies that the constructor telescope contains every declared parameter
binder. -/
theorem stripNestedCtorParameters_success
    (methods : Methods m) :
    ∀ {ty : KExpr m} {remaining : Nat} {result : KExpr m}
        {initial final : TcState m},
      (stripNestedCtorParameters ty remaining).run methods initial =
          .ok result final →
      NestedParameterStripTrace methods ty remaining result initial final
  | ty, 0, result, initial, final, hrun => by
      simp only [stripNestedCtorParameters, pure, ReaderT.run] at hrun
      cases hrun
      exact .done ty initial
  | ty, remaining + 1, result, initial, final, hrun => by
      rw [stripNestedCtorParameters, ReaderT.run_bind, runTcBind] at hrun
      cases hwhnf : (whnf ty).run methods initial with
      | error err afterWhnf =>
          rw [hwhnf] at hrun
          contradiction
      | ok w afterWhnf =>
          rw [hwhnf] at hrun
          cases w with
          | all name bi dom body info =>
              simp only at hrun
              exact .forall hwhnf
                (stripNestedCtorParameters_success methods hrun)
          | var idx name info =>
              simp only [throw, ReaderT.run] at hrun
              contradiction
          | fvar id name info =>
              simp only [throw, ReaderT.run] at hrun
              contradiction
          | sort level info =>
              simp only [throw, ReaderT.run] at hrun
              contradiction
          | const id us info =>
              simp only [throw, ReaderT.run] at hrun
              contradiction
          | app fn arg info =>
              simp only [throw, ReaderT.run] at hrun
              contradiction
          | lam name bi dom body info =>
              simp only [throw, ReaderT.run] at hrun
              contradiction
          | letE name type value body nonDep info =>
              simp only [throw, ReaderT.run] at hrun
              contradiction
          | prj id field value info =>
              simp only [throw, ReaderT.run] at hrun
              contradiction
          | nat value blob info =>
              simp only [throw, ReaderT.run] at hrun
              contradiction
          | str value blob info =>
              simp only [throw, ReaderT.run] at hrun
              contradiction

/-- Every successful recursive nested-field traversal records each WHNF,
field-domain positivity check, dependent binder opening, recursive tail, and
the exact local-context restoration performed by production. -/
theorem checkNestedCtorFieldsLoopFuel_success
    (methods : Methods m) :
    ∀ {fuel : Nat} {ty : KExpr m}
        {groups : Array (PositivityGroup m)} {activeAddrs : Array Address}
        {initial final : TcState m},
      (checkNestedCtorFieldsLoopFuel fuel ty groups activeAddrs).run methods
          initial = .ok () final →
      NestedFieldLoopTrace groups activeAddrs methods fuel ty initial final
  | 0, ty, groups, activeAddrs, initial, final, hrun => by
      simp only [checkNestedCtorFieldsLoopFuel, throw, ReaderT.run] at hrun
      contradiction
  | fuel + 1, ty, groups, activeAddrs, initial, final, hrun => by
      rw [checkNestedCtorFieldsLoopFuel, ReaderT.run_bind, runTcBind] at hrun
      cases hwhnf : (whnf ty).run methods initial with
      | error err afterWhnf =>
          rw [hwhnf] at hrun
          contradiction
      | ok w afterWhnf =>
          rw [hwhnf] at hrun
          cases w with
          | all name bi dom body info =>
              simp only at hrun
              rw [ReaderT.run_bind, runTcBind] at hrun
              cases hdomain :
                  (checkPositivityDomainFuel fuel dom groups activeAddrs).run
                    methods afterWhnf with
              | error err afterDomain =>
                  rw [hdomain] at hrun
                  contradiction
              | ok value afterDomain =>
                  rw [hdomain] at hrun
                  cases value
                  simp only at hrun
                  rw [ReaderT.run_bind] at hrun
                  change EStateM.bind (get : TcM m (TcState m)) _ afterDomain =
                    _ at hrun
                  unfold EStateM.bind at hrun
                  rw [show (get : TcM m (TcState m)) afterDomain =
                    .ok afterDomain afterDomain from rfl] at hrun
                  simp only at hrun
                  rw [ReaderT.run_bind, ReaderT.run_monadLift] at hrun
                  change EStateM.bind (TcM.openBinderAnon dom body) _
                    afterDomain = _ at hrun
                  unfold EStateM.bind at hrun
                  cases hopen : TcM.openBinderAnon dom body afterDomain with
                  | error err afterOpen =>
                      rw [hopen] at hrun
                      contradiction
                  | ok opened afterOpen =>
                      rcases opened with ⟨openBody, fv⟩
                      rw [hopen] at hrun
                      simp only at hrun
                      change (withLctxRestoration afterDomain.lctx.size
                        (checkNestedCtorFieldsLoopFuel fuel openBody groups
                          activeAddrs)).run methods afterOpen = .ok () final at hrun
                      rcases withLctxRestoration_success _ _ _ _ _ hrun with
                        ⟨afterRecursive, hrecursive, hrestored⟩
                      exact .forall hwhnf hdomain hopen
                        (checkNestedCtorFieldsLoopFuel_success methods
                          hrecursive)
                        hrestored
          | var idx name info =>
              simp only [pure, ReaderT.run] at hrun
              cases hrun
              exact .terminal hwhnf trivial
          | fvar id name info =>
              simp only [pure, ReaderT.run] at hrun
              cases hrun
              exact .terminal hwhnf trivial
          | sort level info =>
              simp only [pure, ReaderT.run] at hrun
              cases hrun
              exact .terminal hwhnf trivial
          | const id us info =>
              simp only [pure, ReaderT.run] at hrun
              cases hrun
              exact .terminal hwhnf trivial
          | app fn arg info =>
              simp only [pure, ReaderT.run] at hrun
              cases hrun
              exact .terminal hwhnf trivial
          | lam name bi dom body info =>
              simp only [pure, ReaderT.run] at hrun
              cases hrun
              exact .terminal hwhnf trivial
          | letE name type value body nonDep info =>
              simp only [pure, ReaderT.run] at hrun
              cases hrun
              exact .terminal hwhnf trivial
          | prj id field value info =>
              simp only [pure, ReaderT.run] at hrun
              cases hrun
              exact .terminal hwhnf trivial
          | nat value blob info =>
              simp only [pure, ReaderT.run] at hrun
              cases hrun
              exact .terminal hwhnf trivial
          | str value blob info =>
              simp only [pure, ReaderT.run] at hrun
              cases hrun
              exact .terminal hwhnf trivial

/-- Every successful positive-fuel field transformer reaches the recursive
field loop after exact production instantiation, complete parameter stripping,
and substitution. -/
theorem checkNestedCtorFieldsFuel_success
    {fuel : Nat} {ctorTy : KExpr m} {nParams : Nat}
    {paramArgs : Array (KExpr m)} {us : Array (KUniv m)}
    {groups : Array (PositivityGroup m)} {activeAddrs : Array Address}
    {methods : Methods m} {initial final : TcState m}
    (hrun : (checkNestedCtorFieldsFuel (fuel + 1) ctorTy nParams paramArgs us
      groups activeAddrs).run methods initial = .ok () final) :
    NestedCtorFieldsTrace fuel ctorTy nParams paramArgs us groups activeAddrs
      methods initial final := by
  unfold checkNestedCtorFieldsFuel at hrun
  rw [ReaderT.run_bind, ReaderT.run_monadLift] at hrun
  change EStateM.bind (TcM.instantiateUnivParams ctorTy us) _ initial = _ at hrun
  unfold EStateM.bind at hrun
  cases hinstantiate : TcM.instantiateUnivParams ctorTy us initial with
  | error err afterInstantiation =>
      rw [hinstantiate] at hrun
      contradiction
  | ok instantiated afterInstantiation =>
      rw [hinstantiate] at hrun
      simp only at hrun
      rw [ReaderT.run_bind] at hrun
      change EStateM.bind
        ((stripNestedCtorParameters instantiated nParams).run methods) _
          afterInstantiation = _ at hrun
      unfold EStateM.bind at hrun
      cases hstrip :
          (stripNestedCtorParameters instantiated nParams).run methods
            afterInstantiation with
      | error err afterStripping =>
          rw [hstrip] at hrun
          contradiction
      | ok stripped afterStripping =>
          rw [hstrip] at hrun
          simp only at hrun
          rw [ReaderT.run_bind, ReaderT.run_monadLift] at hrun
          change EStateM.bind
            (TcM.runIntern (simulSubst stripped paramArgs.reverse 0)) _
              afterStripping = _ at hrun
          unfold EStateM.bind at hrun
          cases hsubstitution :
              TcM.runIntern (simulSubst stripped paramArgs.reverse 0)
                afterStripping with
          | error err afterSubstitution =>
              rw [hsubstitution] at hrun
              contradiction
          | ok substituted afterSubstitution =>
              rw [hsubstitution] at hrun
              simp only at hrun
              exact .complete hinstantiate hstrip
                (stripNestedCtorParameters_success methods hstrip)
                hsubstitution hrun
                (checkNestedCtorFieldsLoopFuel_success methods hrun)

/-- Expand a successful per-constructor lookup/field equation into the full
field-transformer trace. -/
theorem completeNestedConstructor_of_trace
    {fuel : Nat} {ctorId : KId m} {nParams : Nat}
    {paramArgs : Array (KExpr m)} {us : Array (KUniv m)}
    {groups : Array (PositivityGroup m)} {activeAddrs : Array Address}
    {methods : Methods m} {initial final : TcState m}
    (trace : NestedConstructorTrace fuel ctorId nParams paramArgs us groups
      activeAddrs methods initial final) :
    CompleteNestedConstructorTrace fuel ctorId nParams paramArgs us groups
      activeAddrs methods initial final := by
  rcases trace with ⟨concrete, ctorTy, afterLookup, hlookup, hheader, hfields⟩
  cases fuel with
  | zero =>
      simp only [checkNestedCtorFieldsFuel, throw, ReaderT.run] at hfields
      contradiction
  | succ innerFuel =>
      exact ⟨innerFuel, concrete, ctorTy, afterLookup, rfl, hlookup, hheader,
        checkNestedCtorFieldsFuel_success hfields⟩

/-- Expand a source-ordered shallow constructor list into the complete list
trace without changing any intermediate checker state. -/
theorem completeNestedConstructorList_of_trace
    {fuel : Nat} {nParams : Nat} {paramArgs : Array (KExpr m)}
    {us : Array (KUniv m)} {groups : Array (PositivityGroup m)}
    {activeAddrs : Array Address} {methods : Methods m}
    {ctors : List (KId m)} {initial final : TcState m}
    (trace : NestedConstructorListTrace fuel nParams paramArgs us groups
      activeAddrs methods ctors initial final) :
    CompleteNestedConstructorListTrace fuel nParams paramArgs us groups
      activeAddrs methods ctors initial final := by
  induction trace with
  | nil state => exact .nil state
  | cons head tail ih =>
      exact .cons (completeNestedConstructor_of_trace head) ih

/-- Expand block discovery and its complete constructor traversal. -/
theorem completeFreshNestedPositivity_of_trace
    {fuel : Nat} {us : Array (KUniv m)} {args : Array (KExpr m)}
    {groups : Array (PositivityGroup m)} {activeAddrs : Array Address}
    {nParams : Nat} {block : KId m} {ctors : Array (KId m)}
    {methods : Methods m} {initial final : TcState m}
    (trace : FreshNestedPositivityTrace fuel us args groups activeAddrs nParams
      block ctors methods initial final) :
    CompleteFreshNestedPositivityTrace fuel us args groups activeAddrs nParams
      block ctors methods initial final := by
  rcases trace with ⟨extBlockInductives, afterDiscovery, hdiscovery, hctors⟩
  exact ⟨extBlockInductives, afterDiscovery, hdiscovery,
    completeNestedConstructorList_of_trace hctors⟩

/-- Expand the successful checked branch, including a fresh specialization's
complete constructor-field traversal. -/
theorem completeNestedPositivityChecked_of_trace
    {fuel : Nat} {id : KId m} {us : Array (KUniv m)}
    {args : Array (KExpr m)} {groups : Array (PositivityGroup m)}
    {rootAddrs activeAddrs : Array Address} {nParams : Nat}
    {block : KId m} {ctors : Array (KId m)} {methods : Methods m}
    {initial final : TcState m}
    (trace : NestedPositivityCheckedTrace fuel id us args groups rootAddrs
      activeAddrs nParams block ctors methods initial final) :
    CompleteNestedPositivityCheckedTrace fuel id us args groups rootAddrs
      activeAddrs nParams block ctors methods initial final := by
  cases trace with
  | existing group state selected indicesIndependent =>
      exact .existing group _ selected indicesIndependent
  | fresh absent parameterMention indicesIndependent continuation =>
      exact .fresh absent parameterMention indicesIndependent
        (completeFreshNestedPositivity_of_trace
          (checkFreshNestedPositivityApplicationFuel_success continuation))

/-- Expand exact header arities and the checked continuation. -/
theorem completeNestedPositivityResolved_of_trace
    {fuel : Nat} {id : KId m} {us : Array (KUniv m)}
    {args : Array (KExpr m)} {groups : Array (PositivityGroup m)}
    {rootAddrs activeAddrs : Array Address} {nParams nIndices levels : Nat}
    {block : KId m} {ctors : Array (KId m)} {methods : Methods m}
    {initial final : TcState m}
    (trace : NestedPositivityResolvedTrace fuel id us args groups rootAddrs
      activeAddrs nParams nIndices levels block ctors methods initial final) :
    CompleteNestedPositivityResolvedTrace fuel id us args groups rootAddrs
      activeAddrs nParams nIndices levels block ctors methods initial final := by
  rcases trace with ⟨hargs, hus, hchecked⟩
  exact ⟨hargs, hus,
    completeNestedPositivityChecked_of_trace
      (checkNestedPositivityApplicationCheckedFuel_success hchecked)⟩

/-- Every successful nested-family application validation exposes the exact
loaded inductive header and the resolved continuation that consumed it. -/
theorem checkNestedPositivityApplicationFuel_success
    {fuel : Nat} {id : KId m} {us : Array (KUniv m)}
    {args : Array (KExpr m)} {groups : Array (PositivityGroup m)}
    {rootAddrs activeAddrs : Array Address} {methods : Methods m}
    {initial final : TcState m}
    (hrun : (checkNestedPositivityApplicationFuel fuel id us args groups
      rootAddrs activeAddrs).run methods initial = .ok () final) :
    NestedPositivityApplicationTrace fuel id us args groups rootAddrs
      activeAddrs methods initial final := by
  unfold checkNestedPositivityApplicationFuel at hrun
  simp only [ReaderT.run_bind, ReaderT.run_monadLift, monadLift_self] at hrun
  change EStateM.bind (TcM.getConst id) _ initial = _ at hrun
  unfold EStateM.bind at hrun
  cases hlookup : TcM.getConst id initial with
  | error err afterLookup =>
      rw [hlookup] at hrun
      contradiction
  | ok concrete afterLookup =>
      rw [hlookup] at hrun
      cases concrete with
      | indc name levelParams lvls params indices isUnsafe block memberIdx ty
          ctors leanAll =>
          simp only at hrun
          exact ⟨.indc name levelParams lvls params indices isUnsafe block
              memberIdx ty ctors leanAll,
            params.toNat, indices.toNat, lvls.toNat, block, ctors,
            afterLookup, hlookup, ⟨rfl, rfl, rfl, rfl, rfl⟩, hrun⟩
      | defn name levelParams kind safety hints lvls ty value leanAll block =>
          change EStateM.Result.error _ afterLookup = .ok () final at hrun
          contradiction
      | recr name levelParams k isUnsafe lvls params indices motives minors
          block memberIdx ty rules leanAll =>
          change EStateM.Result.error _ afterLookup = .ok () final at hrun
          contradiction
      | axio name levelParams isUnsafe lvls ty =>
          change EStateM.Result.error _ afterLookup = .ok () final at hrun
          contradiction
      | quot name levelParams kind lvls ty =>
          change EStateM.Result.error _ afterLookup = .ok () final at hrun
          contradiction
      | ctor name levelParams isUnsafe lvls induct cidx params fields ty =>
          change EStateM.Result.error _ afterLookup = .ok () final at hrun
          contradiction

/-- A successful production nested-family action has a complete trace from
header lookup through every recursively traversed constructor field. -/
theorem checkNestedPositivityApplicationFuel_complete
    {fuel : Nat} {id : KId m} {us : Array (KUniv m)}
    {args : Array (KExpr m)} {groups : Array (PositivityGroup m)}
    {rootAddrs activeAddrs : Array Address} {methods : Methods m}
    {initial final : TcState m}
    (hrun : (checkNestedPositivityApplicationFuel fuel id us args groups
      rootAddrs activeAddrs).run methods initial = .ok () final) :
    CompleteNestedPositivityApplicationTrace fuel id us args groups rootAddrs
      activeAddrs methods initial final := by
  rcases checkNestedPositivityApplicationFuel_success hrun with
    ⟨concrete, nParams, nIndices, levels, block, ctors, afterLookup,
      hlookup, hheader, hresolved⟩
  exact ⟨concrete, nParams, nIndices, levels, block, ctors, afterLookup,
    hlookup, hheader,
    completeNestedPositivityResolved_of_trace
      (checkNestedPositivityApplicationResolvedFuel_success hresolved)⟩

end RecM
end Ix.Tc
