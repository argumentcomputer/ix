import Compilatrix.Pipeline

namespace Compilatrix.Pipeline

open Compilatrix.Ixon (Address Constant Owned)

/-! ## End-to-end integration fixture

A two-constructor `Box` block gives the first constructor a unique
result/field world and the second a shared result/field world. Its
identity-like recursor rebuilds either major with the shared constructor.
`dropFirst : Box →ᵃ Box →ω Box`
discards its affine first argument and returns its shared second one;
`main` constructs both boxes, calls `dropFirst`, then runs the block
recursor on the survivor.

The fixture forces all integration seams at once: the checker accepts
the mixed modes, the eraser emits a real recursor declaration, the
lowerer consumes that declaration, and the IxIR₁ runtime observes one
unique deep-free plus shared RC traffic. -/

section Guards

private def address (byte : UInt8) : Address := Address.replicate byte

private def aBlock := address 0x70
private def aBox := address 0x71
private def aCtor := address 0x72
private def aRec := address 0x73
private def aDropFirst := address 0x74
private def aMain := address 0x75
private def aEleven := address 0x76
private def aTwentyTwo := address 0x77
private def aUnused := address 0x78
private def aSharedCtor := address 0x79

private def boxType : Ixon.Expr := .ref 0 #[]

private def boxInductive : Ixon.Inductive :=
  { isUnsafe := false, lvls := 0, params := 0, indices := 0
    typ := .sort 0
    ctors := #[
      { isUnsafe := false, lvls := 0, cidx := 0, params := 0, fields := 1
        typ := .all .affine .unique (.sort 0) (.recur 0 #[]) },
      { isUnsafe := false, lvls := 0, cidx := 1, params := 0, fields := 1
        typ := .all .many .shared (.sort 0) (.recur 0 #[]) }
    ] }

/-- `Box.rec box = Box.mk box.field`, deliberately nontrivial so the
lowered case body allocates a fresh shared result. -/
private def boxRecursor : Ixon.Recursor :=
  { k := false, isUnsafe := false, lvls := 0
    params := 0, indices := 0, motives := 0, minors := 0
    typ := .all .many .shared (.recur 0 #[]) (.recur 0 #[])
    rules := #[
      { fields := 1
        rhs := .lam .many (.sort 0) (.app (.ref 0 #[]) (.var 0)) },
      { fields := 1
        rhs := .lam .many (.sort 0) (.app (.ref 0 #[]) (.var 0)) }
    ] }

private def cBlock : Constant :=
  { info := .muts #[.indc boxInductive, .recr boxRecursor]
    sharing := #[], refs := #[aSharedCtor], univs := #[.zero] }

private def projection (info : Ixon.ConstantInfo) : Constant :=
  { info, sharing := #[], refs := #[], univs := #[] }

private def cBox :=
  projection (.iPrj { idx := 0, block := aBlock })

private def cCtor :=
  projection (.cPrj { idx := 0, cidx := 0, block := aBlock })

private def cSharedCtor :=
  projection (.cPrj { idx := 0, cidx := 1, block := aBlock })

private def cRec :=
  projection (.rPrj { idx := 1, block := aBlock })

private def dropFirstValue : Ixon.Expr :=
  .lam .affine boxType (.lam .many boxType (.var 0))

private def cDropFirst : Constant :=
  { info := .defn
      { kind := .defn, safety := .safe, lvls := 0
        typ := .all .affine .shared boxType
          (.all .many .shared boxType boxType)
        value := dropFirstValue }
    sharing := #[], refs := #[aBox], univs := #[.zero] }

private def boxOfNat (blobRef : UInt64) : Ixon.Expr :=
  .app (.ref 2 #[]) (.nat blobRef)

/-- Manufacture a checker-shared, computational Nat field without an
implicit freeze: projection is a shared borrow, and its temporary unique
box is lowered in the projection's shared demand. -/
private def sharedBoxOfNat (blobRef : UInt64) : Ixon.Expr :=
  .app (.ref 6 #[]) (.prj 0 0 (boxOfNat blobRef))

private def cMain : Constant :=
  { info := .defn
      { kind := .defn, safety := .safe, lvls := 0
        typ := .ref 0 #[]
        value := .app (.ref 3 #[])
          (.app (.app (.ref 1 #[]) (boxOfNat 4)) (sharedBoxOfNat 5)) }
    sharing := #[]
    refs := #[aBox, aDropFirst, aCtor, aRec, aEleven, aTwentyTwo,
      aSharedCtor]
    univs := #[.zero] }

/-- A validated function deliberately absent from main's transitive runtime
references. The compiler emits it; rooted reachability must remove
its lowered declaration rather than relying only on a hand-written graph. -/
private def cUnused : Constant :=
  { info := .defn
      { kind := .defn, safety := .safe, lvls := 0
        typ := .all .many .shared boxType boxType
        value := .lam .many boxType
          (.app (.ref 1 #[]) (.var 0)) }
    sharing := #[]
    refs := #[aBox, aRec]
    univs := #[.zero] }

/-- A usage-valid shared constructor result whose lowered main contains no
dynamic application. The surrounding catalog still emits stored functions,
so it gives rooted reachability an observable compiler-produced deletion. -/
private def cReachMain : Constant :=
  { cMain with
    info := .defn
      { kind := .defn, safety := .safe, lvls := 0
        typ := .ref 0 #[]
        value := sharedBoxOfNat 4 } }

private def constants : List (Address × Constant) :=
  [(aBlock, cBlock), (aBox, cBox), (aCtor, cCtor),
   (aSharedCtor, cSharedCtor), (aRec, cRec),
   (aDropFirst, cDropFirst), (aMain, cMain)]

private def blobs : Address → Option Ixon.Eval.Blob := fun a =>
  if a == aEleven then some (.natB 11)
  else if a == aTwentyTwo then some (.natB 22)
  else none

/-! Exact structural-budget boundary fixtures.  Every field is set to the
measured requirement of this program; lowering any one field by one must name
that precise metric, actual value, and limit before checking begins. -/

private def budgetStats : Ixon.Work.ProgramStats :=
  Ixon.Work.programStats constants

private def exactLimits : Limits :=
  { maxConstants := budgetStats.constants
    maxExpressionUnits := budgetStats.expressionUnits
    maxExpandedExpressionUnits := budgetStats.expandedExpressionUnits
    maxLayer1NodeVisits := budgetStats.layer1NodeVisits
    maxErasedDeclarations := budgetStats.erasedDeclarations
    maxErasureAppendCells := budgetStats.erasureAppendCells
    maxCertificateCandidates := budgetStats.certificateCandidates
    maxCertificateValidationAttempts :=
      budgetStats.certificateValidationAttempts
    maxCertificateSourceNodeWork := budgetStats.certificateSourceNodeWork
    maxUsageFuel := Ixon.UsageCheck.defaultFuel
    maxErasureFuel := Erase.defaultFuel
    maxValidationFuel := Erase.defaultFuel
    maxLoweringFuel := 10000 }

private def validatedPreflight (limits : Limits) :
    Except Error Ixon.Work.ProgramStats :=
  preflightValidated limits constants Ixon.UsageCheck.defaultFuel
    Erase.defaultFuel Erase.defaultFuel 10000

private def rejectsResource (metric : Ixon.Work.Metric)
    (actual limit : Nat) (result : Except Error Ixon.Work.ProgramStats) : Bool :=
  match result with
  | .error (.resource exceeded) =>
    exceeded.metric == metric && exceeded.actual == actual &&
      exceeded.limit == limit
  | _ => false

private def exactBudgetAccepted : Bool :=
  match validatedPreflight exactLimits with
  | .ok stats => stats == budgetStats
  | .error _ => false

private def everyOneBelowBudgetRejected : Bool :=
  let s := budgetStats
  #[
    rejectsResource .programConstants s.constants (s.constants - 1)
      (validatedPreflight
        { exactLimits with maxConstants := s.constants - 1 }),
    rejectsResource .programExpressionUnits s.expressionUnits
      (s.expressionUnits - 1)
      (validatedPreflight
        { exactLimits with maxExpressionUnits := s.expressionUnits - 1 }),
    rejectsResource .programExpandedExpressionUnits s.expandedExpressionUnits
      (s.expandedExpressionUnits - 1)
      (validatedPreflight
        { exactLimits with maxExpandedExpressionUnits :=
            s.expandedExpressionUnits - 1 }),
    rejectsResource .layer1NodeVisits s.layer1NodeVisits
      (s.layer1NodeVisits - 1)
      (validatedPreflight
        { exactLimits with maxLayer1NodeVisits := s.layer1NodeVisits - 1 }),
    rejectsResource .usageFuel Ixon.UsageCheck.defaultFuel
      (Ixon.UsageCheck.defaultFuel - 1)
      (validatedPreflight
        { exactLimits with maxUsageFuel := Ixon.UsageCheck.defaultFuel - 1 }),
    rejectsResource .erasedDeclarations s.erasedDeclarations
      (s.erasedDeclarations - 1)
      (validatedPreflight
        { exactLimits with maxErasedDeclarations := s.erasedDeclarations - 1 }),
    rejectsResource .erasureAppendCells s.erasureAppendCells
      (s.erasureAppendCells - 1)
      (validatedPreflight
        { exactLimits with maxErasureAppendCells :=
            s.erasureAppendCells - 1 }),
    rejectsResource .erasureFuel Erase.defaultFuel
      (Erase.defaultFuel - 1)
      (validatedPreflight
        { exactLimits with maxErasureFuel := Erase.defaultFuel - 1 }),
    rejectsResource .loweringFuel 10000 9999
      (validatedPreflight { exactLimits with maxLoweringFuel := 9999 }),
    rejectsResource .certificateCandidates s.certificateCandidates
      (s.certificateCandidates - 1)
      (validatedPreflight
        { exactLimits with maxCertificateCandidates :=
            s.certificateCandidates - 1 }),
    rejectsResource .certificateValidationAttempts
      s.certificateValidationAttempts (s.certificateValidationAttempts - 1)
      (validatedPreflight
        { exactLimits with maxCertificateValidationAttempts :=
            s.certificateValidationAttempts - 1 }),
    rejectsResource .certificateSourceNodeWork s.certificateSourceNodeWork
      (s.certificateSourceNodeWork - 1)
      (validatedPreflight
        { exactLimits with maxCertificateSourceNodeWork :=
            s.certificateSourceNodeWork - 1 }),
    rejectsResource .validationFuel Erase.defaultFuel
      (Erase.defaultFuel - 1)
      (validatedPreflight
        { exactLimits with maxValidationFuel := Erase.defaultFuel - 1 })
  ].all id

#guard exactBudgetAccepted
#guard everyOneBelowBudgetRejected

private def compiled : Except Error Artifact :=
  compile constants aMain { blobs }

/-- The source evaluator returns the box built from the second
argument, after rebuilding it through the recursor. -/
private def sourceAgrees : Bool :=
  let resolverIndex := ResolverIndex.ofList constants
  let ctx : Ixon.Eval.EvalCtx := { resolve := resolverIndex.resolve, blobs }
  let frame : Ixon.Eval.Frame := { refs := #[aMain] }
  match Ixon.Eval.evalClosed ctx frame (.ref 0 #[]) with
  | .ok (.ctorV block 0 1 [.litV (.natL 22)]) => block == aBlock
  | _ => false

/-- The actual erased recursor reaches IxIR₁ as a unary `case`
function; this is not a hand-written IxIR₀ recursor fixture. -/
private def recursorCrossesBothPasses : Bool :=
  match compiled with
  | .error _ => false
  | .ok artifact =>
    let transient := Erase.memberAddr aBlock 1
    match artifact.erasedAddressMap.lookup transient,
        artifact.rawErasedDecls.find? (fun entry => entry.1 == transient) with
    | some member, some (_, .recursor 0 false rawRules) =>
      match artifact.erasedDecls.find? (fun entry => entry.1 == member),
          artifact.targetAddressMap.lookup member with
      | some (_, .recursor 0 false rules), some targetMember =>
        match artifact.targetDecls.find? (fun entry =>
            entry.1 == targetMember) with
        | some (_, .fn fn) =>
          member != transient && targetMember != member &&
          artifact.erasedBlocks.length == 1 &&
          rawRules.size == 2 && rules.size == 2 && fn.arity == 1 &&
          !(artifact.erasedDecls.map (·.1)).contains transient &&
          !(artifact.targetDecls.map (·.1)).contains transient &&
          !(artifact.targetDecls.map (·.1)).contains member &&
          match fn.body with
          | .case _ false alts => alts.size == 2
          | _ => false
        | _ => false
      | _, _ => false
    | _, _ => false

/-- Runtime result and cost facts for the composed pipeline. Before
releasing the result: two input boxes + one pap + one rebuilt box were
allocated; the unique input, pap, and shared major were reclaimed.
Releasing the result leaves an empty store. -/
private def targetAgrees : Bool :=
  match compiled with
  | .error _ => false
  | .ok artifact =>
    let targetIndex := IxIR1.Env.Index.ofList artifact.targetDecls
    let ctx : IxIR1.Ctx := { decls := targetIndex.toEnv }
    match IxIR1.runMain ctx artifact.main with
    | .ok (store, value@(.loc location)) =>
      let shape := match store.get? location with
        | some box =>
          match box.node with
          | .ctorN cid fields =>
            cid.block == aSharedCtor && cid.cidx == 1 &&
              fields.toList == [.lit (.nat 22)]
          | _ => false
        | none => false
      shape && store.allocs == 5 && store.frees == 4 &&
        store.rcops == 3 && store.live == 1 &&
        match IxIR1.dropVal ctx 100000 store value with
        | .ok released =>
          released.allocs == 5 && released.frees == 5 &&
            released.rcops == 4 && released.live == 0
        | .error _ => false
    | _ => false

/-- Optimizer observations run on actual compiler output, not only a
hand-written IxIR₁ graph. Independent runs must agree byte-for-byte on their
reports and output roots; disabling the pass must select the exact input
graph. -/
private def optimizerHarnessOnCompiled : Bool :=
  match compiled with
  | .error _ => false
  | .ok artifact =>
      match artifact.produceHPT with
      | .error _ => false
      | .ok production =>
          let (firstArtifact, firstReport) :=
            artifact.optimizeWithProducedHPT IxIR1.Optimizer.defaultPolicy
              production
          let (repeatArtifact, repeatReport) :=
            artifact.optimizeWithProducedHPT IxIR1.Optimizer.defaultPolicy
              production
          let disabledPolicy : IxIR1.Optimizer.Policy :=
            { casePrune := { enabled := false }
              fetchForward := { enabled := false }
              destruction := { enabled := false }
              papFuse := { enabled := false }
              reachability := { enabled := false } }
          let (disabledArtifact, disabledReport) :=
            artifact.optimizeWithProducedHPT disabledPolicy production
          let inputRoot := IxIR1.Optimizer.graphRoot artifact.targetArtifacts
            artifact.main
          let firstRoot := IxIR1.Optimizer.graphRoot
            firstArtifact.targetArtifacts firstArtifact.main
          let repeatRoot := IxIR1.Optimizer.graphRoot
            repeatArtifact.targetArtifacts repeatArtifact.main
          firstReport.before.functions > 0 &&
            firstReport.before.counts.instructions > 0 &&
            firstReport.before.codeBytes > 0 &&
            firstReport.certificateBytes > 0 &&
            firstReport.inputRoot == inputRoot &&
            firstReport.outputRoot == firstRoot &&
            firstReport.after == IxIR1.Optimizer.observe
              firstArtifact.targetArtifacts firstArtifact.main &&
            firstRoot == repeatRoot &&
            firstReport.bytes == repeatReport.bytes &&
            firstReport.address == repeatReport.address &&
            disabledReport.disposition ==
              .skipped IxIR1.Optimizer.SkipReason.disabled &&
            disabledReport.inputRoot == inputRoot &&
            disabledReport.outputRoot == inputRoot &&
            IxIR1.Optimizer.graphRoot disabledArtifact.targetArtifacts
              disabledArtifact.main == inputRoot

private def destructionCid : IxIR1.CtorId :=
  { block := address 0x7d, indIdx := 0, cidx := 0 }

/-- The first binding proves scalar-drop elimination; the unique allocation
proves exact all-scalar leaf destruction.  Keeping both in `main` exercises
the sentinel analysis owner as well as the empty-program rebuild path. -/
private def destructionMain : IxIR1.Code :=
  .letOp (.pure (.lit (.nat 5)))
    (.letOp (.drop (.var 0))
      (.letOp (.alloc .unique destructionCid #[.lit (.nat 7)])
        (.letOp (.dropU (.var 0))
          (.ret (.lit (.nat 42))))))

private def destructionRuntimeOk (code : IxIR1.Code) : Bool :=
  match IxIR1.runMain { decls := IxIR1.Env.empty } code with
  | .ok (store, .lit (.nat 42)) =>
      store.allocs == 1 && store.frees == 1 && store.rcops == 0 &&
        store.live == 0
  | _ => false

/-- Checked production specializes both destructor sites, attributes the
changes, preserves the exact executable observation, and reaches a structural
fixed point on the immediately rechecked output. -/
private def optimizerSpecializesDestruction : Bool :=
  match IxIR1.HPT.produce ([] : List IxIR1.ReaddressAll.Artifact) with
  | .error _ => false
  | .ok production =>
      let first := IxIR1.Optimizer.runWithProducedHPT
        IxIR1.Optimizer.defaultPolicy [] destructionMain production
      let optimizedMain := first.main destructionMain
      let second := IxIR1.Optimizer.runWithProducedHPT
        IxIR1.Optimizer.defaultPolicy [] optimizedMain production
      let unsupportedPolicy : IxIR1.Optimizer.Policy :=
        { destruction := { version := 0 } }
      let unsupported := IxIR1.Optimizer.runWithProducedHPT
        unsupportedPolicy [] destructionMain production
      destructionRuntimeOk destructionMain &&
        destructionRuntimeOk optimizedMain &&
        first.report.disposition == .changed &&
        first.report.elidedScalarDrops == 1 &&
        first.report.specializedUniqueDrops == 1 &&
        first.report.before.counts.rcDecrements == 1 &&
        first.report.before.counts.uniqueDrops == 1 &&
        first.report.before.counts.frees == 0 &&
        first.report.after.counts.rcDecrements == 0 &&
        first.report.after.counts.uniqueDrops == 0 &&
        first.report.after.counts.frees == 1 &&
        second.report.disposition == .unchanged &&
        second.report.elidedScalarDrops == 0 &&
        second.report.specializedUniqueDrops == 0 &&
        second.report.inputRoot == second.report.outputRoot &&
        (second.main optimizedMain).bytes == optimizedMain.bytes &&
        unsupported.rebuilt.isNone &&
        unsupported.report.disposition ==
          .skipped (.unsupportedDestructionVersion 0
            IxIR1.Optimizer.currentDestructionVersion)

private def reachabilityConstants : List (Address × Constant) :=
  [(aBlock, cBlock), (aBox, cBox), (aCtor, cCtor),
   (aSharedCtor, cSharedCtor), (aRec, cRec),
   (aDropFirst, cDropFirst), (aMain, cReachMain),
   (aUnused, cUnused)]

/-- Production Ixon→IxIR₁ compilation emits stored functions which the
default rooted pass then removes. This closes the compiler-emitted witness,
rather than relying only on a hand-written IxIR₁ declaration graph. -/
private def compilerReachabilityRemovesUnused : Bool :=
  match compile reachabilityConstants aMain { blobs } with
  | .error _ => false
  | .ok artifact =>
      match artifact.produceHPT with
      | .error _ => false
      | .ok production =>
          let (optimized, report) := artifact.optimizeWithProducedHPT
            IxIR1.Optimizer.defaultPolicy production
          let ctx : IxIR1.Ctx := { decls := optimized.targetDeclEnv }
          let result := IxIR1.runMain ctx optimized.main
          report.disposition == .changed &&
            report.removedDeclarations == 5 &&
            report.before.functions == 6 && report.after.functions == 1 &&
            match result with
            | .ok (store, .loc location) =>
                match store.get? location with
                | some box =>
                    match box.node with
                    | .ctorN cid fields =>
                        cid.block == aSharedCtor && cid.cidx == 1 &&
                          fields.toList == [.lit (.nat 11)]
                    | _ => false
                | none => false
            | _ => false

/-- A double use of the affine parameter is stopped at the first
pipeline gate, before erasure or lowering can observe the program. -/
private def badDropFirst : Constant :=
  { cDropFirst with
    info := .defn
      { kind := .defn, safety := .safe, lvls := 0
        typ := .all .affine .shared boxType
          (.all .many .shared boxType boxType)
        value := .lam .affine boxType
          (.lam .many boxType (.app (.var 1) (.var 1))) } }

private def rejectsBadUsage : Bool :=
  let bad := constants.map fun entry =>
    if entry.1 == aDropFirst then (aDropFirst, badDropFirst) else entry
  match compile bad aMain { blobs } with
  | .error (.usage address (.binderCovers .affine .many)) =>
    address == aDropFirst
  | _ => false

#guard sourceAgrees

/-! ### The validated entry point

The same mixed-mode/add fixture must compile identically through
`compileValidated` (every constant of the fixture is inside the
validator's fragment), and one out-of-fragment declaration must flip
the verdict between the two entry points. -/

private def validated : Except Error Artifact :=
  compileValidated constants aMain { blobs }

/-- `compileValidated` reproduces `compile` on the in-fragment
fixture: the same erased declarations, the same target addresses, and
the same runtime result and cost facts as `targetAgrees` pins. -/
private def validatedAgrees : Bool :=
  match compiled, validated with
  | .ok direct, .ok gated =>
    direct.rawErasedDecls == gated.rawErasedDecls &&
    direct.erasedDecls == gated.erasedDecls &&
    direct.erasedAddressMap == gated.erasedAddressMap &&
    direct.targetAddressMap == gated.targetAddressMap &&
    direct.targetBlocks.map (·.blockAddress) ==
      gated.targetBlocks.map (·.blockAddress) &&
    direct.targetDecls.map (·.1) == gated.targetDecls.map (·.1) &&
    (let targetIndex := IxIR1.Env.Index.ofList gated.targetDecls
     let ctx : IxIR1.Ctx := { decls := targetIndex.toEnv }
     match IxIR1.runMain ctx gated.main with
     | .ok (store, .loc location) =>
       (match store.get? location with
        | some box =>
          match box.node with
          | .ctorN cid fields =>
            cid.block == aSharedCtor && cid.cidx == 1 &&
              fields.toList == [.lit (.nat 22)]
          | _ => false
        | none => false) &&
       store.allocs == 5 && store.frees == 4 && store.rcops == 3 &&
       store.live == 1
     | _ => false)
  | _, _ => false

/-- An axiom is UsageCheck-clean and erases to an extern, so the
unvalidated pipeline accepts it. The certified pipeline rejects the exact
addressed extern graph before lowering and retains that check as a proof field. -/
private def aGhostAxiom := address 0x7c

private def cGhostAxiom : Constant :=
  { info := .axio { isUnsafe := false, lvls := 0, typ := .sort 0 }
    sharing := #[], refs := #[], univs := #[] }

private def outOfFragment : List (Address × Constant) :=
  constants ++ [(aGhostAxiom, cGhostAxiom)]

private def acceptsOutOfFragment : Bool :=
  match compile outOfFragment aMain { blobs } with
  | .ok _ => true
  | .error _ => false

private def rejectsOutOfFragment : Bool :=
  match compileValidated outOfFragment aMain { blobs } with
  | .error (.validate rejected message) =>
    rejected == aGhostAxiom &&
      message == "validated extern ownership ABI rejects this declaration"
  | _ => false

/-- Native integration fixtures are evaluated by the compiled test executable:
the cycle-safe block pass invokes the BLAKE3 FFI and therefore cannot live in
an elaboration-time `#guard`. -/
def nativeIntegrationChecks : List (String × Bool) :=
  [("addressed recursor crosses erasure and lowering",
      recursorCrossesBothPasses),
   ("addressed pipeline runtime and cost", targetAgrees),
   ("compiler-produced optimizer report is deterministic and disable-safe",
      optimizerHarnessOnCompiled),
   ("checked optimizer specializes exact destruction and reaches a fixed point",
      optimizerSpecializesDestruction),
   ("compiler-emitted unreachable declarations are removed",
      compilerReachabilityRemovesUnused),
   ("usage rejection precedes addressed erasure", rejectsBadUsage),
   ("validated and direct addressed pipelines agree", validatedAgrees),
   ("unvalidated addressed pipeline accepts configured fragment",
      acceptsOutOfFragment),
   ("validated addressed pipeline rejects uncovered extern",
      rejectsOutOfFragment)]

end Guards

end Compilatrix.Pipeline
