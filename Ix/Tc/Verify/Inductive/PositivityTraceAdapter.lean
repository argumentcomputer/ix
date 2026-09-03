import Ix.Tc.Verify.Inductive.RecursivePositivityTraversal
import Lean4Lean.Inductive.ValidationTrace

/-!
# Transporting production positivity into Lean4Lean's retained trace

`PositivityDomainTrace` records the successful Ix execution, while
Lean4Lean's `ConstructorPositivityTrace` records the corresponding successful
Lean-kernel execution.  These traces cannot be cast into one another: they use
different expression representations, local contexts, reducers, and state
models.

This module isolates the exact cross-kernel obligations and proves the
recursive assembly once.  `FlatPositivityTraceTransport` is deliberately
operation-shaped: it relates expressions, one WHNF execution, one opened Pi,
and one validated direct application.  It does not contain a field that can
return an entire positivity trace.  The theorem below performs the fuel
recursion itself.

The current theorem covers the root-free, forall, and direct-family cases.
Nested applications are excluded by the explicit
`FlatPositivityDomainTrace`; their transport must be constructed from
certified flat-block auxiliary expansion rather than supplied through this
interface.
-/

namespace Ix.Tc

/-- Exact successful production positivity traversal for the flat fragment.

This is a separate trace rather than a predicate indexed by a
`PositivityDomainTrace` proof. Both production traces live in `Prop`, so proof
irrelevance prevents soundly distinguishing one proof by its constructor
shape. The erasure theorem below embeds this trace in the exhaustive one. -/
inductive FlatPositivityDomainTrace
    (groups : Array (PositivityGroup m)) (activeAddrs : Array Address)
    (methods : Methods m) :
    Nat → KExpr m → TcState m → TcState m → Prop
  | rootFree {fuel : Nat} {source : KExpr m}
      {rootGroup : PositivityGroup m} {state : TcState m}
      (root : groups[0]? = some rootGroup)
      (free : exprMentionsAnyAddr source rootGroup.addrs = false) :
      FlatPositivityDomainTrace groups activeAddrs methods (fuel + 1) source
        state state
  | forall {fuel : Nat} {source : KExpr m}
      {name : m.F Name} {bi : m.F Lean.BinderInfo}
      {innerDom innerBody innerOpen : KExpr m} {info : ExprInfo m}
      {fv : FVarId} {rootGroup : PositivityGroup m}
      {initial afterWhnf afterOpen afterRecursive final : TcState m}
      (root : groups[0]? = some rootGroup)
      (mentioned : exprMentionsAnyAddr source rootGroup.addrs = true)
      (whnf : (RecM.whnf source).run methods initial =
        .ok (.all name bi innerDom innerBody info) afterWhnf)
      (domainFree : exprMentionsAnyAddr innerDom rootGroup.addrs = false)
      (opening : TcM.openBinderAnon innerDom innerBody afterWhnf =
        .ok (innerOpen, fv) afterOpen)
      (tail : FlatPositivityDomainTrace groups activeAddrs methods fuel innerOpen
        afterOpen afterRecursive)
      (restored : final = { afterRecursive with
        lctx := afterRecursive.lctx.truncate afterWhnf.lctx.size }) :
      FlatPositivityDomainTrace groups activeAddrs methods (fuel + 1) source
        initial final
  | application {fuel : Nat} {source w : KExpr m}
      {id : KId m} {us : Array (KUniv m)} {info : ExprInfo m}
      {args : Array (KExpr m)} {rootGroup : PositivityGroup m}
      {initial afterWhnf final : TcState m}
      (root : groups[0]? = some rootGroup)
      (mentioned : exprMentionsAnyAddr source rootGroup.addrs = true)
      (whnf : (RecM.whnf source).run methods initial = .ok w afterWhnf)
      (notForall : PositivityTerminalForm w)
      (spine : w.collectSpine = (.const id us info, args))
      (active : rootGroup.addrs.contains id.addr = true)
      (valid : ValidPositiveRecursiveApplication id us args groups
        rootGroup.addrs methods afterWhnf final) :
      FlatPositivityDomainTrace groups activeAddrs methods (fuel + 1) source
        initial final

namespace FlatPositivityDomainTrace

/-- Forgetting the flat-fragment refinement yields the exhaustive successful
production trace. -/
theorem toPositivityDomainTrace
    (trace : FlatPositivityDomainTrace groups activeAddrs methods fuel source
      initial final) :
    PositivityDomainTrace groups activeAddrs methods fuel source initial
      final := by
  induction trace with
  | rootFree root free => exact .rootFree root free
  | «forall» root mentioned whnf domainFree opening tail restored tailFull =>
      exact .forall root mentioned whnf domainFree opening tailFull restored
  | application root mentioned whnf notForall spine active valid =>
      exact .application root mentioned whnf notForall spine
        (.direct active valid)

end FlatPositivityDomainTrace

/-- Primitive cross-kernel correspondence needed to transport the flat
positivity fragment.

`SourceRel` is indexed by the current Ix state and Lean4Lean constructor
context so the forall field must relate the *actual* free variable allocated
by each checker. `ResultRel` separately relates the one WHNF result consumed
by the branch discriminator. Keeping these phases distinct avoids demanding
that a post-WHNF cache state be closed under an execution that production
never performs. The direct field consumes Ix's already-proved logical
recursive-application invariant; it may not assume the final Lean4Lean trace
itself. -/
structure FlatPositivityTraceTransport
    (stats : Lean4Lean.AddInductive.InductiveStats)
    (rootAddrs : Array Address) (methods : Methods .anon)
    (SourceRel ResultRel : TcState .anon → Lean4Lean.AddInductive.Context →
      KExpr .anon → Lean.Expr → Prop) : Prop where
  /-- A syntactically root-free Ix domain has a corresponding successful
  Lean4Lean WHNF result with no occurrence of the flat block.  Establishing
  this field requires the declaration-order/freshness argument that reduction
  of an older constant cannot introduce a newly declared family. -/
  rootFree : ∀ {ixState leanContext ixSource leanSource},
    SourceRel ixState leanContext ixSource leanSource →
    exprMentionsAnyAddr ixSource rootAddrs = false →
    ∃ leanResult,
      Lean4Lean.AddInductive.CandidateWhnfStep.Valid
        ⟨leanContext, leanSource, leanResult⟩ ∧
      Lean4Lean.AddInductive.hasIndOcc stats.indConsts leanResult = false

  /-- One exact successful production WHNF execution on a root-mentioning
  source corresponds to one exact successful Lean4Lean candidate-WHNF
  execution, and their results remain related in the post-Ix state.

  Production checks occurrence before entering this branch.  Retaining that
  guard avoids demanding reducer simulation for related root-free expressions,
  which are discharged by `rootFree` without running the Ix reducer. -/
  whnf : ∀ {ixBefore ixAfter leanContext ixSource ixResult leanSource},
    SourceRel ixBefore leanContext ixSource leanSource →
    exprMentionsAnyAddr ixSource rootAddrs = true →
    (RecM.whnf ixSource).run methods ixBefore = .ok ixResult ixAfter →
    ∃ leanResult,
      Lean4Lean.AddInductive.CandidateWhnfStep.Valid
        ⟨leanContext, leanSource, leanResult⟩ ∧
      ResultRel ixAfter leanContext ixResult leanResult

  /-- The expression relation preserves the exact root-block occurrence
  decision. -/
  mentions : ∀ {ixState leanContext ixExpr leanExpr},
    SourceRel ixState leanContext ixExpr leanExpr →
    exprMentionsAnyAddr ixExpr rootAddrs =
      Lean4Lean.AddInductive.hasIndOcc stats.indConsts leanExpr

  /-- A related Ix forall is a Lean forall.  Its domains are related, and the
  two checkers' concrete binder-opening operations produce related bodies in
  the exact extended Lean4Lean context. -/
  forallE : ∀ {ixState leanContext ixName ixBinder ixDomain ixBody ixInfo
      leanExpr},
    ResultRel ixState leanContext
      (.all ixName ixBinder ixDomain ixBody ixInfo) leanExpr →
    ∃ leanName leanBinder leanDomain leanBody,
      leanExpr = .forallE leanName leanDomain leanBody leanBinder ∧
      SourceRel ixState leanContext ixDomain leanDomain ∧
      ∀ {ixOpen : KExpr .anon} {ixFVar : FVarId}
          {ixAfterOpen : TcState .anon},
        TcM.openBinderAnon ixDomain ixBody ixState =
          .ok (ixOpen, ixFVar) ixAfterOpen →
        SourceRel ixAfterOpen
          (leanContext.pushLocalDecl leanName leanBinder
            (Lean4Lean.AddInductive.consumeTypeAnnotations leanDomain))
          ixOpen (leanBody.instantiate1 leanContext.freshExpr)

  /-- A production-validated active-family application becomes a valid flat
  Lean4Lean target at the same related WHNF node.  Parameter/universe
  uniformity and index independence must be discharged from `valid`; they are
  not hidden in a whole-trace premise. -/
  direct : ∀ {ixState leanContext ixResult leanResult id us info args groups
      final},
    ResultRel ixState leanContext ixResult leanResult →
    ixResult.collectSpine = (.const id us info, args) →
    rootAddrs.contains id.addr = true →
    ValidPositiveRecursiveApplication id us args groups rootAddrs methods
      ixState final →
    ∃ targetIdx,
      Lean4Lean.AddInductive.hasIndOcc stats.indConsts leanResult = true ∧
      leanResult.isForall = false ∧
      Lean4Lean.AddInductive.isValidIndApp? stats leanResult = some targetIdx

namespace FlatPositivityTraceTransport

/-- Assemble Lean4Lean's exact retained positivity trace from a direct-only
successful production trace.

The result is wrapped in `Nonempty` because the Ix execution trace lives in
`Prop`; this keeps the recursion within propositional elimination while still
supplying the Type-valued Lean4Lean trace to downstream semantic consumers. -/
theorem constructorPositivityTrace
    {stats : Lean4Lean.AddInductive.InductiveStats}
    {rootAddrs : Array Address} {methods : Methods .anon}
    {SourceRel ResultRel : TcState .anon →
      Lean4Lean.AddInductive.Context →
      KExpr .anon → Lean.Expr → Prop}
    (transport : FlatPositivityTraceTransport stats rootAddrs methods
      SourceRel ResultRel) :
    ∀ {groups : Array (PositivityGroup .anon)}
      {activeAddrs : Array Address} {fuel : Nat}
      {ixSource : KExpr .anon} {ixInitial ixFinal : TcState .anon}
      {leanContext : Lean4Lean.AddInductive.Context}
      {leanSource : Lean.Expr} {ctor : Lean.Name} {argIdx : Nat}
      (_trace : FlatPositivityDomainTrace groups activeAddrs methods fuel ixSource
        ixInitial ixFinal),
      groups[0]?.map (·.addrs) = some rootAddrs →
      SourceRel ixInitial leanContext ixSource leanSource →
      Nonempty (Lean4Lean.AddInductive.ConstructorPositivityTrace stats ctor
        argIdx leanContext leanSource fuel)
  | groups, activeAddrs, _, _, _, _, leanContext, leanSource, ctor, argIdx,
      .rootFree (fuel := innerFuel) (rootGroup := rootGroup) root free,
      rootMatches, related => by
      have rootAddrsEq : rootGroup.addrs = rootAddrs := by
        simpa [root] using rootMatches
      obtain ⟨leanResult, leanWhnf, leanFree⟩ :=
        transport.rootFree related (by simpa [rootAddrsEq] using free)
      exact ⟨.absent leanContext leanSource leanResult innerFuel leanWhnf
        leanFree⟩
  | groups, activeAddrs, _, _, _, _, leanContext, leanSource, ctor, argIdx,
      .forall (fuel := innerFuel) (rootGroup := rootGroup) root mentioned
        ixWhnf domainFree opening tail restored,
      rootMatches, related => by
      have rootAddrsEq : rootGroup.addrs = rootAddrs := by
        simpa [root] using rootMatches
      obtain ⟨leanResult, leanWhnf, resultRelated⟩ :=
        transport.whnf related (by simpa [rootAddrsEq] using mentioned) ixWhnf
      obtain ⟨leanName, leanBinder, leanDomain, leanBody, resultEq,
          domainRelated, openRelated⟩ := transport.forallE resultRelated
      subst leanResult
      have leanDomainFree :
          Lean4Lean.AddInductive.hasIndOcc stats.indConsts leanDomain =
            false := by
        rw [← transport.mentions domainRelated]
        simpa [rootAddrsEq] using domainFree
      have tailRelated := openRelated opening
      obtain ⟨leanTail⟩ := constructorPositivityTrace transport tail
        rootMatches tailRelated
      cases leanOccurs : Lean4Lean.AddInductive.hasIndOcc stats.indConsts
          (.forallE leanName leanDomain leanBody leanBinder) with
      | false =>
          exact ⟨.absent leanContext leanSource
            (.forallE leanName leanDomain leanBody leanBinder) innerFuel
            leanWhnf leanOccurs⟩
      | true =>
          exact ⟨.forallE leanContext leanSource innerFuel leanName leanDomain
            leanBody leanBinder leanWhnf leanOccurs leanDomainFree leanTail⟩
  | groups, activeAddrs, _, _, _, _, leanContext, leanSource, ctor, argIdx,
      .application (fuel := innerFuel) (rootGroup := rootGroup) root mentioned
        ixWhnf notForall spine active valid,
      rootMatches, related => by
      have rootAddrsEq : rootGroup.addrs = rootAddrs := by
        simpa [root] using rootMatches
      obtain ⟨leanResult, leanWhnf, resultRelated⟩ :=
        transport.whnf related (by simpa [rootAddrsEq] using mentioned) ixWhnf
      obtain ⟨targetIdx, leanOccurs, leanTerminal, leanValid⟩ :=
        transport.direct resultRelated spine
          (by simpa [rootAddrsEq] using active)
          (by simpa [rootAddrsEq] using valid)
      exact ⟨.target leanContext leanSource leanResult innerFuel targetIdx
        leanWhnf leanOccurs leanTerminal leanValid⟩

end FlatPositivityTraceTransport

/-! ## Flattened nested applications -/

/-- Cross-kernel correspondence for the complete production positivity
traversal after nested-inductive elimination.

The inherited fields retain the operation-shaped flat transport.  The one new
field handles precisely the production branch in which an external family
application is replaced by a generated member of the flat mutual block.  It
consumes the complete nested execution (including header lookup, parameter
stripping, substitution, and recursive constructor traversal) and may return
only the terminal facts for that *one* flattened application.  In particular,
it cannot return a `ConstructorPositivityTrace`; recursive trace assembly
remains the theorem below.

Concrete instances must derive this field from an exact auxiliary request,
its `NestedAuxiliaryHeaderRel`, physical `FlatAuxPresent` evidence, and the
candidate-level relation identifying that member with the Lean4Lean target.
This makes the flat-block correspondence visible at the only control-flow
point where the two kernels' source syntax differs. -/
structure FlattenedPositivityTraceTransport
    (stats : Lean4Lean.AddInductive.InductiveStats)
    (rootAddrs : Array Address) (methods : Methods .anon)
    (SourceRel ResultRel : TcState .anon → Lean4Lean.AddInductive.Context →
      KExpr .anon → Lean.Expr → Prop) : Prop
    extends FlatPositivityTraceTransport stats rootAddrs methods SourceRel
      ResultRel where
  /-- A successfully traversed external-family application corresponds to
  the exact generated auxiliary target present in the flattened candidate. -/
  nested : ∀ {fuel ixState leanContext ixResult leanResult id us info args
      groups activeAddrs final},
    ResultRel ixState leanContext ixResult leanResult →
    ixResult.collectSpine = (.const id us info, args) →
    rootAddrs.contains id.addr = false →
    CompleteNestedPositivityApplicationTrace fuel id us args groups rootAddrs
      activeAddrs methods ixState final →
    ∃ targetIdx,
      Lean4Lean.AddInductive.hasIndOcc stats.indConsts leanResult = true ∧
      leanResult.isForall = false ∧
      Lean4Lean.AddInductive.isValidIndApp? stats leanResult = some targetIdx

namespace FlattenedPositivityTraceTransport

/-- Assemble Lean4Lean's retained positivity trace from the exhaustive
production traversal, including applications eliminated into exact generated
flat auxiliaries.

As in the direct-only adapter, `Nonempty` keeps elimination of the
proof-valued Ix trace within `Prop` while exposing Lean4Lean's Type-valued
trace to the enclosing constructor-validation proof. -/
theorem constructorPositivityTrace
    {stats : Lean4Lean.AddInductive.InductiveStats}
    {rootAddrs : Array Address} {methods : Methods .anon}
    {SourceRel ResultRel : TcState .anon →
      Lean4Lean.AddInductive.Context →
      KExpr .anon → Lean.Expr → Prop}
    (transport : FlattenedPositivityTraceTransport stats rootAddrs methods
      SourceRel ResultRel) :
    ∀ {groups : Array (PositivityGroup .anon)}
      {activeAddrs : Array Address} {fuel : Nat}
      {ixSource : KExpr .anon} {ixInitial ixFinal : TcState .anon}
      {leanContext : Lean4Lean.AddInductive.Context}
      {leanSource : Lean.Expr} {ctor : Lean.Name} {argIdx : Nat}
      (_trace : PositivityDomainTrace groups activeAddrs methods fuel ixSource
        ixInitial ixFinal),
      groups[0]?.map (·.addrs) = some rootAddrs →
      SourceRel ixInitial leanContext ixSource leanSource →
      Nonempty (Lean4Lean.AddInductive.ConstructorPositivityTrace stats ctor
        argIdx leanContext leanSource fuel)
  | groups, activeAddrs, _, _, _, _, leanContext, leanSource, ctor, argIdx,
      .rootFree (fuel := innerFuel) (rootGroup := rootGroup) root free,
      rootMatches, related => by
      have rootAddrsEq : rootGroup.addrs = rootAddrs := by
        simpa [root] using rootMatches
      obtain ⟨leanResult, leanWhnf, leanFree⟩ :=
        transport.rootFree related (by simpa [rootAddrsEq] using free)
      exact ⟨.absent leanContext leanSource leanResult innerFuel leanWhnf
        leanFree⟩
  | groups, activeAddrs, _, _, _, _, leanContext, leanSource, ctor, argIdx,
      .forall (fuel := innerFuel) (rootGroup := rootGroup) root mentioned
        ixWhnf domainFree opening tail restored,
      rootMatches, related => by
      have rootAddrsEq : rootGroup.addrs = rootAddrs := by
        simpa [root] using rootMatches
      obtain ⟨leanResult, leanWhnf, resultRelated⟩ :=
        transport.whnf related (by simpa [rootAddrsEq] using mentioned) ixWhnf
      obtain ⟨leanName, leanBinder, leanDomain, leanBody, resultEq,
          domainRelated, openRelated⟩ := transport.forallE resultRelated
      subst leanResult
      have leanDomainFree :
          Lean4Lean.AddInductive.hasIndOcc stats.indConsts leanDomain =
            false := by
        rw [← transport.mentions domainRelated]
        simpa [rootAddrsEq] using domainFree
      have tailRelated := openRelated opening
      obtain ⟨leanTail⟩ := constructorPositivityTrace transport tail
        rootMatches tailRelated
      cases leanOccurs : Lean4Lean.AddInductive.hasIndOcc stats.indConsts
          (.forallE leanName leanDomain leanBody leanBinder) with
      | false =>
          exact ⟨.absent leanContext leanSource
            (.forallE leanName leanDomain leanBody leanBinder) innerFuel
            leanWhnf leanOccurs⟩
      | true =>
          exact ⟨.forallE leanContext leanSource innerFuel leanName leanDomain
            leanBody leanBinder leanWhnf leanOccurs leanDomainFree leanTail⟩
  | groups, activeAddrs, _, _, _, _, leanContext, leanSource, ctor, argIdx,
      .application (fuel := innerFuel) (rootGroup := rootGroup) root mentioned
        ixWhnf notForall spine terminal,
      rootMatches, related => by
      have rootAddrsEq : rootGroup.addrs = rootAddrs := by
        simpa [root] using rootMatches
      obtain ⟨leanResult, leanWhnf, resultRelated⟩ :=
        transport.whnf related (by simpa [rootAddrsEq] using mentioned) ixWhnf
      obtain ⟨targetIdx, leanOccurs, leanTerminal, leanValid⟩ := by
        cases terminal with
        | direct active valid =>
            exact transport.direct resultRelated spine
              (by simpa [rootAddrsEq] using active)
              (by simpa [rootAddrsEq] using valid)
        | nested inactive nestedTrace =>
            exact transport.nested resultRelated spine
              (by simpa [rootAddrsEq] using inactive)
              (by simpa [rootAddrsEq] using nestedTrace)
      exact ⟨.target leanContext leanSource leanResult innerFuel targetIdx
        leanWhnf leanOccurs leanTerminal leanValid⟩

end FlattenedPositivityTraceTransport

end Ix.Tc
