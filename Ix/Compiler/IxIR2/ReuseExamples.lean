import Ix.Compiler.IxIR1.Lower
import Ix.Compiler.IxIR2.Lower
import Ix.Compiler.IxIR2.Reuse

/-!
# First compiler-emitted dynamic-reuse benchmark

This fixture begins with a hand-written IxIR₀ recursor declaration, not an
IxIR₁ or IxIR₂ loop.  The ordinary IxIR₀→IxIR₁ compiler emits the shared
field-retain/release/allocation recursion shape, the baseline IxIR₁→IxIR₂
lowerer emits and validates its CFG, and `IxIR2.Reuse.optimize` recognizes and
validates the reset/reuse diamond.

The unaliased run takes the hot branch for every cons and performs no fresh
loop allocation.  A second source main deliberately retains the original
list in a returned pair; ownership propagation makes every reset cold and
leaves allocation counts equal to the baseline.  Both cases compare the
IxIR₀ source observation, baseline IxIR₂ observation, rewritten logical
observation, and rewritten physical observation before reclaiming every
returned target heap.
-/

namespace Ix.Compiler.IxIR2.Reuse.Examples

open Ix.Compiler.Ixon (Address Owned)
open Ix.Compiler.IxIR2

def nilAddress : Address := Address.replicate 0xd1
def consAddress : Address := Address.replicate 0xd2
def reverseAddress : Address := Address.replicate 0xd3
def pairAddress : Address := Address.replicate 0xd4
def otherConsAddress : Address := Address.replicate 0xd5

def nilId : CtorId := IxIR1.Lower.ctorIdOf nilAddress 0
def consId : CtorId := IxIR1.Lower.ctorIdOf consAddress 1
def pairId : CtorId := IxIR1.Lower.ctorIdOf pairAddress 0
def otherConsId : CtorId := IxIR1.Lower.ctorIdOf otherConsAddress 1

def nilLayout : LayoutId := Address.replicate 0xe1
def consLayout : LayoutId := Address.replicate 0xe2
def pairLayout : LayoutId := Address.replicate 0xe3
def otherConsLayout : LayoutId := Address.replicate 0xe4

private def app2 (fn left right : IxIR0.Expr) : IxIR0.Expr :=
  .app (.app fn left) right

private def cons (head tail : IxIR0.Expr) : IxIR0.Expr :=
  app2 (.ref consAddress) head tail

private def pair (left right : IxIR0.Expr) : IxIR0.Expr :=
  app2 (.ref pairAddress) left right

private def list (values : List Nat) : IxIR0.Expr :=
  values.foldr (fun value tail => cons (.lit (.nat value)) tail)
    (.ref nilAddress)

/-- Rule environment: tail, head, accumulator, recursive self. -/
def reverseConsRule : IxIR0.RecRule :=
  { fields := 2
    rhs := app2 (.var 3) (cons (.var 1) (.var 2)) (.var 0) }

/-- The source declaration inventory.  Reversal is a genuine IxIR₀
recursor with the accumulator before the major premise. -/
def sourceDeclarations : List (Address × IxIR0.Decl) :=
  [(nilAddress, .ctor 0 0),
   (consAddress, .ctor 1 2),
   (pairAddress, .ctor 0 2),
   (reverseAddress, .recursor 1 false #[
      { fields := 0, rhs := .var 0 },
      reverseConsRule])]

def unaliasedMain : IxIR0.Expr :=
  app2 (.ref reverseAddress) (.ref nilAddress) (list [1, 2, 3])

/-- `xs` is consumed once by reversal and once by the result pair.  The
IxIR₀→IxIR₁ compiler inserts the root retain; cold resets propagate that
second ownership through the tail. -/
def aliasedMain : IxIR0.Expr :=
  .letE .many (list [1, 2, 3])
    (.letE .many
      (app2 (.ref reverseAddress) (.ref nilAddress) (.var 0))
      (pair (.var 0) (.var 1)))

def loweringContext : Ix.Compiler.IxIR2.Lower.Context :=
  { parameterWorlds := fun address =>
      if address == reverseAddress then some #[.shared, .shared]
      else none
    schemas := fun world identity =>
      if world != .shared then none
      else if identity == nilId then
        some { layout := nilLayout, fields := #[] }
      else if identity == consId then
        some { layout := consLayout, fields := #[.shared, .shared] }
      else if identity == pairId then
        some { layout := pairLayout, fields := #[.shared, .shared] }
      else
        none
    caseCtors := fun _ alternative =>
      if alternative == 0 then [nilId]
      else if alternative == 1 then [consId]
      else [] }

inductive CompileError where
  | ixir1 (message : String)
  | baseline (error : Ix.Compiler.IxIR2.Lower.Error)
  | reuse (error : Reuse.Error)
  deriving Repr

/-- All retained target artifacts come from executable compiler/checker APIs;
the structure contains no hand-written IxIR₁ or IxIR₂ code. -/
structure Compiled (source : IxIR0.Expr) where
  input : Ix.Compiler.IxIR2.Lower.Input
  baseline : Ix.Compiler.IxIR2.Lower.Checked
  optimized : Reuse.Output Validate.defaultLimits
    baseline.artifact.validationContext baseline.artifact.program

def compile (source : IxIR0.Expr) : Except CompileError (Compiled source) :=
  match IxIR1.Lower.lowerAll sourceDeclarations source .shared with
  | .error message => .error (.ixir1 message)
  | .ok (declarations, main) =>
      let input : Ix.Compiler.IxIR2.Lower.Input :=
        { declarations, main, mainResult := .shared }
      match Ix.Compiler.IxIR2.Lower.lowerChecked loweringContext input with
      | .error error => .error (.baseline error)
      | .ok baseline =>
          match Reuse.optimize baseline.artifact.validationContext
              baseline.artifact.program with
          | .error error => .error (.reuse error)
          | .ok optimized => .ok { input, baseline, optimized }

private def sourceNats? : Nat → IxIR0.Value → Option (List Nat)
  | 0, _ => none
  | fuel + 1, .ctor address tag values =>
      if address == nilAddress && tag == 0 && values.isEmpty then
        some []
      else if address == consAddress && tag == 1 then
        match values with
        | [.lit (.nat head), tail] =>
            (sourceNats? fuel tail).map (head :: ·)
        | _ => none
      else
        none
  | _, _ => none

private def sourcePair? (fuel : Nat) : IxIR0.Value →
    Option (List Nat × List Nat)
  | .ctor address tag [left, right] =>
      if address == pairAddress && tag == 0 then do
        return (← sourceNats? fuel left, ← sourceNats? fuel right)
      else
        none
  | _ => none

private def targetNats? : Nat → Eval.Store → Eval.RVal →
    Option (List Nat)
  | 0, _, _ => none
  | fuel + 1, store, .loc location => do
      let box ← store.get? location
      match box.node with
      | .ctorN identity values =>
          if identity == nilId && values.isEmpty then
            some []
          else if identity == consId then
            match values.toList with
            | [.lit (.nat head), tail] =>
                (targetNats? fuel store tail).map (head :: ·)
            | _ => none
          else
            none
      | .papN .. => none
  | _, _, _ => none

private def targetPair? (fuel : Nat) (store : Eval.Store) : Eval.RVal →
    Option (List Nat × List Nat)
  | .loc location => do
      let box ← store.get? location
      match box.node with
      | .ctorN identity values =>
          if identity == pairId then
            match values.toList with
            | [left, right] =>
                return (← targetNats? fuel store left,
                  ← targetNats? fuel store right)
            | _ => none
          else
            none
      | .papN .. => none
  | _ => none

private def sourceContext : IxIR0.Ctx :=
  { env := IxIR0.Env.ofList sourceDeclarations }

private def targetContext (context : Validate.Context)
    (program : Program) : Eval.Context :=
  Eval.Context.ofProgram program context.schemas

private def released (result : Eval.Result) : Bool :=
  match Eval.releaseShared 1000 result.store result.value with
  | .ok (store, _) => store.live == 0
  | .error _ => false

private def terminalCounterLaw (logical physical : Eval.Result) : Bool :=
  let left := logical.store.counters
  let right := physical.store.counters
  left.allocs == right.allocs + right.reuses &&
    left.frees == right.frees + right.reuses &&
    left.rcops == right.rcops &&
    logical.store.live == physical.store.live &&
    left.resetAttempts == right.resetAttempts &&
    left.hotResets == right.hotResets &&
    left.coldResets == right.coldResets

private def expectedReport : Reuse.Report :=
  { scannedBlocks := 4
    shapeCandidates := 1
    rewritten := 1
    incompatibleLayouts := 0
    helperBlocks := 2 }

def ternarySourceAddress : Address := Address.replicate 0xd6
def ternaryAllocationAddress : Address := Address.replicate 0xd7
def ternaryFunctionAddress : Address := Address.replicate 0xd8
def ternaryLayout : LayoutId := Address.replicate 0xe6

def ternarySourceId : CtorId :=
  IxIR1.Lower.ctorIdOf ternarySourceAddress 0

def ternaryAllocationId : CtorId :=
  IxIR1.Lower.ctorIdOf ternaryAllocationAddress 0

private def ownedSharedParam : Param :=
  { world := .shared, passing := .owned }

/-- A valid non-benchmark shape with three fields and the consumed source in
parameter register one.  Allocation and tail arguments are both permuted. -/
def ternaryBlock : Block :=
  { valueParams := #[.owned .shared, .owned .shared, .owned .shared]
    creditParams := #[]
    instructions := #[
      .fetch (.reg 1) ternarySourceId 0,
      .fetch (.reg 1) ternarySourceId 1,
      .fetch (.reg 1) ternarySourceId 2,
      .retainShared (.reg 3),
      .retainShared (.reg 4),
      .retainShared (.reg 5),
      .releaseShared (.reg 1),
      .alloc .shared ternaryAllocationId #[.reg 8, .reg 0, .reg 6]]
    terminator := .tailCallSelf #[.reg 2, .reg 9, .reg 7] }

def ternaryFunction : Function :=
  { signature :=
      { params := #[ownedSharedParam, ownedSharedParam, ownedSharedParam]
        result := .shared
        papSafe := false }
    blocks := #[ternaryBlock] }

private def trivialMain : Function :=
  { signature := { params := #[], result := .shared, papSafe := false }
    blocks := #[
      { valueParams := #[]
        creditParams := #[]
        instructions := #[.alloc .shared nilId #[]]
        terminator := .ret (.reg 0) }] }

def ternaryProgram : Program :=
  { declarations := [(ternaryFunctionAddress, .fn ternaryFunction)]
    main := trivialMain }

def ternaryContext : Validate.Context :=
  { schemas := fun world identity =>
      if world != .shared then none
      else if identity == ternarySourceId then
        some { layout := ternaryLayout,
               fields := #[.shared, .shared, .shared] }
      else if identity == ternaryAllocationId then
        some { layout := ternaryLayout,
               fields := #[.shared, .shared, .shared] }
      else if identity == nilId then
        some { layout := nilLayout, fields := #[] }
      else
        none }

/-- The generalized matcher consumes checked liveness and preserves register
meaning across a nonzero source parameter, three fields, and permutations. -/
def generalizedShapeAccepted : Bool :=
  match Reuse.optimize ternaryContext ternaryProgram with
  | .error _ => false
  | .ok output =>
      output.report ==
        { scannedBlocks := 2
          shapeCandidates := 1
          rewritten := 1
          helperBlocks := 2 } &&
      match output.target.declarations with
      | [(_, .fn definition)] =>
          match definition.blocks[0]?, definition.blocks[1]?,
              definition.blocks[2]? with
          | some reset, some hot, some cold =>
              reset.instructions == #[
                .resetShared (.reg 1) ternarySourceId] &&
              reset.terminator == .branchCredit 0
                { target := 1
                  values := #[.reg 3, .reg 4, .reg 5, .reg 0, .reg 2]
                  credits := #[0] }
                { target := 2
                  values := #[.reg 3, .reg 4, .reg 5, .reg 0, .reg 2]
                  credits := #[0] } &&
              hot.valueParams == Array.replicate 5 (.owned .shared) &&
              hot.creditParams == #[.required ternaryLayout] &&
              hot.instructions == #[
                .allocWith 0 .shared ternaryAllocationId
                  #[.reg 2, .reg 3, .reg 0]] &&
              hot.terminator == .tailCallSelf #[.reg 4, .reg 5, .reg 1] &&
              cold.valueParams == hot.valueParams &&
              cold.creditParams == #[.optional ternaryLayout] &&
              cold.instructions == hot.instructions &&
              cold.terminator == hot.terminator
          | _, _, _ => false
      | _ => false

def ternaryRewrite :
    Reuse.FunctionRewrite Validate.defaultLimits ternaryContext ternaryFunction :=
  Reuse.rewriteFunction Validate.defaultLimits ternaryContext ternaryFunction

/-- The proof-facing traversal retains an accepted dependent site for the
generalized three-field block, not merely a positive report counter.  The
general `FunctionRewrite.acceptedAt` theorem turns this constructor into exact
reset/hot/cold target-block lookups. -/
def generalizedDecisionTraceAccepted : Bool :=
  match ternaryRewrite.decisions with
  | .cons (.accepted _) .nil => true
  | _ => false

/-- Even a syntactic prefix is left untouched when its source appears after
the proposed release.  This exercises the liveness gate independently of the
whole-program validator, which would also reject this malformed ownership
flow. -/
def lateSourceUseRejected : Bool :=
  let lateBlock : Block :=
    { ternaryBlock with
      terminator := .tailCallSelf #[.reg 1, .reg 9, .reg 7] }
  let lateFunction : Function :=
    { ternaryFunction with blocks := #[lateBlock] }
  let source : Program :=
    { ternaryProgram with declarations :=
        [(ternaryFunctionAddress, .fn lateFunction)] }
  let rewrite := Reuse.rewriteProgram ternaryContext source
  rewrite.program == source &&
    rewrite.report ==
      { scannedBlocks := 2
        shapeCandidates := 1
        livenessRejected := 1 }

/-- Structural evidence that the optimizer consumed the baseline compiler
shape and emitted the optional-credit diamond, rather than benchmarking a
prewritten reset program. -/
def compilerShapeAndDiamond (compiled : Compiled source) : Bool :=
  let baselineShape :=
    match compiled.baseline.artifact.program.declarations.find? fun entry =>
        entry.1 == reverseAddress with
    | some (_, .fn definition) =>
        match definition.blocks[2]? with
        | some block =>
            block.instructions == #[
              .fetch (.reg 0) consId 0,
              .fetch (.reg 0) consId 1,
              .retainShared (.reg 2),
              .retainShared (.reg 3),
              .releaseShared (.reg 0),
              .alloc .shared consId #[.reg 4, .reg 1]] &&
              block.terminator == .tailCallSelf #[.reg 6, .reg 5]
        | none => false
    | _ => false
  let targetShape :=
    match compiled.optimized.target.declarations.find? fun entry =>
        entry.1 == reverseAddress with
    | some (_, .fn definition) =>
        match definition.blocks[2]?, definition.blocks[3]?,
            definition.blocks[4]? with
        | some reset, some hot, some cold =>
            reset.instructions == #[.resetShared (.reg 0) consId] &&
              reset.terminator == .branchCredit 0
                { target := 3
                  values := #[.reg 2, .reg 3, .reg 1]
                  credits := #[0] }
                { target := 4
                  values := #[.reg 2, .reg 3, .reg 1]
                  credits := #[0] } &&
              hot.creditParams == #[.required consLayout] &&
              hot.instructions == #[
                .allocWith 0 .shared consId #[.reg 0, .reg 2]] &&
              cold.creditParams == #[.optional consLayout] &&
              cold.instructions == #[
                .allocWith 0 .shared consId #[.reg 0, .reg 2]]
        | _, _, _ => false
    | _ => false
  baselineShape && targetShape &&
    compiled.optimized.report == expectedReport &&
    let rerun := Reuse.rewriteProgram
      compiled.baseline.artifact.validationContext compiled.optimized.target
    rerun.program == compiled.optimized.target && rerun.report.rewritten == 0

private def runTargets (compiled : Compiled source) :
    Except Eval.Error (Eval.Result × Eval.Result × Eval.Result) := do
  let baselineProgram := compiled.baseline.artifact.program
  let context := compiled.baseline.artifact.validationContext
  let optimizedProgram := compiled.optimized.target
  let baseline ← Eval.runMain (targetContext context baselineProgram)
    .logical baselineProgram 100 100
  let logical ← Eval.runMain (targetContext context optimizedProgram)
    .logical optimizedProgram 100 100
  let physical ← Eval.runMain (targetContext context optimizedProgram)
    .physical optimizedProgram 100 100
  return (baseline, logical, physical)

/-- Hot-path benchmark: source/baseline/logical/physical results all reverse
the list, all returned heaps reclaim fully, and the physical loop turns all
three replacement allocations into reuse. -/
def unaliasedBenchmark : Bool :=
  match sourceContext.run unaliasedMain 1000, compile unaliasedMain with
  | .ok source, .ok compiled =>
      compilerShapeAndDiamond compiled &&
        match runTargets compiled with
        | .ok (baseline, logical, physical) =>
            sourceNats? 100 source == some [3, 2, 1] &&
              targetNats? 100 baseline.store baseline.value ==
                some [3, 2, 1] &&
              targetNats? 100 logical.store logical.value ==
                some [3, 2, 1] &&
              targetNats? 100 physical.store physical.value ==
                some [3, 2, 1] &&
              baseline.store.counters.allocs == 8 &&
              baseline.store.counters.reuses == 0 &&
              baseline.store.counters.frees == 4 &&
              baseline.store.counters.rcops == 10 &&
              baseline.store.counters.resetAttempts == 0 &&
              baseline.store.peakLiveNodes == 5 &&
              logical.store.counters.allocs == 8 &&
              logical.store.counters.reuses == 0 &&
              logical.store.counters.frees == 4 &&
              logical.store.counters.rcops == 1 &&
              physical.store.counters.allocs == 5 &&
              physical.store.counters.reuses == 3 &&
              physical.store.counters.frees == 1 &&
              physical.store.counters.rcops == 1 &&
              physical.store.counters.resetAttempts == 3 &&
              physical.store.counters.hotResets == 3 &&
              physical.store.counters.coldResets == 0 &&
              physical.store.counters.reusedPayloadUnits == 6 &&
              physical.store.peakLiveNodes == 5 &&
              terminalCounterLaw logical physical &&
              released baseline && released logical && released physical
        | .error _ => false
  | _, _ => false

/-- Cold-path benchmark: retaining the original list makes every attempt
cold.  The rewritten program allocates exactly as much as the baseline,
returns both lists unchanged, and fully reclaims both result graphs. -/
def aliasedBenchmark : Bool :=
  match sourceContext.run aliasedMain 1000, compile aliasedMain with
  | .ok source, .ok compiled =>
      compilerShapeAndDiamond compiled &&
        match runTargets compiled with
        | .ok (baseline, logical, physical) =>
            sourcePair? 100 source == some ([3, 2, 1], [1, 2, 3]) &&
              targetPair? 100 baseline.store baseline.value ==
                some ([3, 2, 1], [1, 2, 3]) &&
              targetPair? 100 logical.store logical.value ==
                some ([3, 2, 1], [1, 2, 3]) &&
              targetPair? 100 physical.store physical.value ==
                some ([3, 2, 1], [1, 2, 3]) &&
              baseline.store.counters.allocs == 9 &&
              baseline.store.counters.reuses == 0 &&
              baseline.store.counters.frees == 0 &&
              baseline.store.counters.rcops == 8 &&
              baseline.store.counters.resetAttempts == 0 &&
              baseline.store.peakLiveNodes == 9 &&
              logical.store.counters.allocs == 9 &&
              logical.store.counters.reuses == 0 &&
              logical.store.counters.frees == 0 &&
              logical.store.counters.rcops == 8 &&
              physical.store.counters.allocs == baseline.store.counters.allocs &&
              physical.store.counters.reuses == 0 &&
              physical.store.counters.frees == 0 &&
              physical.store.counters.rcops == 8 &&
              physical.store.counters.resetAttempts == 3 &&
              physical.store.counters.hotResets == 0 &&
              physical.store.counters.coldResets == 3 &&
              physical.store.peakLiveNodes == 9 &&
              terminalCounterLaw logical physical &&
              released baseline && released logical && released physical
        | .error _ => false
  | _, _ => false

private def zeroFieldChildAddress : Address := Address.replicate 0xd9

/-- The nil branch has no generated fetches. Its accepted prefix instead
consumes the second inherited parameter; the recursive call swaps the result
into the scrutinee position and exits through the cons branch. -/
private def zeroFieldChildBody : IxIR1.Code :=
  .case (.var 0) false #[
    .mk 0 0
      (.letOp (.fetch (.var 1) 0)
        (.letOp (.fetch (.var 2) 1)
          (.letOp (.dup (.var 1))
            (.letOp (.dup (.var 1))
              (.letOp (.drop (.var 5))
                (.letOp (.alloc .shared consId #[.var 2, .var 1])
                  (.letOp (.callSelf #[.var 6, .var 0])
                    (.ret (.var 0))))))))),
    .mk 1 2 (.letOp (.drop (.var 3)) (.ret (.var 3)))]

private def zeroFieldChildMain (aliased : Bool) : IxIR1.Code :=
  .letOp (.alloc .shared nilId #[])
    (.letOp (.alloc .shared nilId #[])
      (.letOp (.alloc .shared consId #[.lit (.nat 42), .var 0])
        (if aliased then
          .letOp (.dup (.var 0))
            (.letOp (.call zeroFieldChildAddress #[.var 0, .var 3])
              (.letOp (.alloc .shared pairId #[.var 0, .var 2])
                (.ret (.var 0))))
        else
          .letOp (.call zeroFieldChildAddress #[.var 0, .var 2])
            (.ret (.var 0)))))

private def zeroFieldChildInput (aliased : Bool) : Lower.Input :=
  { declarations :=
      [(zeroFieldChildAddress,
        .fn { arity := 2, result := .shared, papSafe := false,
              body := zeroFieldChildBody })]
    main := zeroFieldChildMain aliased
    mainResult := .shared }

private def zeroFieldChildContext : Lower.Context :=
  { loweringContext with
    parameterWorlds := fun address =>
      if address == zeroFieldChildAddress then some #[.shared, .shared]
      else none
    fetchCtor := fun site =>
      if site.owner == .declaration zeroFieldChildAddress &&
          site.branches == [0] && site.offset < 2 then some consId
      else none }

/-- This bounded fixture starts at IxIR₁. Both compiler checks and the reuse
validator must accept its empty generated prologue before runtime comparison. -/
private def zeroFieldChildCompile (aliased : Bool) : Except CompileError
    (Sigma fun baseline : Lower.Checked =>
      Reuse.Output Validate.defaultLimits baseline.artifact.validationContext
        baseline.artifact.program) := do
  let baseline ← (Lower.lowerChecked zeroFieldChildContext
    (zeroFieldChildInput aliased)).mapError CompileError.baseline
  let optimized ← (Reuse.optimize baseline.artifact.validationContext
    baseline.artifact.program).mapError CompileError.reuse
  return ⟨baseline, optimized⟩

private def zeroFieldChildShape (baseline : Lower.Checked)
    (optimized : Reuse.Output Validate.defaultLimits
      baseline.artifact.validationContext baseline.artifact.program) : Bool :=
  optimized.report == expectedReport &&
    match baseline.artifact.trace.functions.find? (fun trace =>
        trace.owner == .declaration zeroFieldChildAddress),
      optimized.target.declarations.find? (fun entry =>
        entry.1 == zeroFieldChildAddress) with
    | some trace, some (_, .fn definition) =>
        trace.root.switchBranchesMatch &&
          match trace.root, definition.blocks[1]? with
          | .switchValue _ _ _ _ _ _ _ _ parent _ children, some reset =>
              (match parent.terminator, children[0]? with
              | .switchValue _ alternatives _, some child =>
                  child.targetPosition == .instruction 0 && child.headBlock.1 == 1 &&
                    (match alternatives[0]? with
                    | some alternative => alternative.cid == nilId &&
                        alternative.edge.target == 1
                    | none => false) &&
                    child.headBlock.2.instructions[0]? ==
                      some (.fetch (.reg 1) consId 0)
              | _, _ => false) &&
                reset.instructions == #[.resetShared (.reg 1) consId]
          | _, _ => false
    | _, _ => false

/-- Empty constructor prologues can lead to hot or cold reuse of a different
inherited node. Compare both observations and reclaim every returned heap. -/
def zeroFieldChildBenchmark (aliased : Bool) : Bool :=
  match zeroFieldChildCompile aliased with
  | .error _ => false
  | .ok ⟨baseline, optimized⟩ =>
      zeroFieldChildShape baseline optimized &&
        let baselineProgram := baseline.artifact.program
        let context := baseline.artifact.validationContext
        match Eval.runMain (targetContext context baselineProgram)
            .physical baselineProgram 100 100,
          Eval.runMain (targetContext context optimized.target)
            .logical optimized.target 100 100,
          Eval.runMain (targetContext context optimized.target)
            .physical optimized.target 100 100 with
        | .ok baseline, .ok logical, .ok physical =>
            let observed (result : Eval.Result) :=
              if aliased then
                targetPair? 100 result.store result.value ==
                  some ([42], [42])
              else
                targetNats? 100 result.store result.value == some [42]
            observed baseline && observed logical && observed physical &&
              baseline.store.counters.allocs == (if aliased then 5 else 4) &&
              baseline.store.counters.resetAttempts == 0 &&
              physical.store.counters.allocs == (if aliased then 5 else 3) &&
              physical.store.counters.reuses == (if aliased then 0 else 1) &&
              physical.store.counters.resetAttempts == 1 &&
              physical.store.counters.hotResets == (if aliased then 0 else 1) &&
              physical.store.counters.coldResets == (if aliased then 1 else 0) &&
              terminalCounterLaw logical physical &&
              released baseline && released logical && released physical
        | _, _, _ => false

private def incompatibleProgram (program : Program) : Program :=
  { program with
    declarations := program.declarations.map fun entry =>
      if entry.1 != reverseAddress then entry
      else
        match entry.2 with
        | .extern _ => entry
        | .fn definition =>
            match definition.blocks[2]? with
            | none => entry
            | some block =>
                let instructions := block.instructions.setIfInBounds 5
                  (.alloc .shared otherConsId #[.reg 4, .reg 1])
                let replacement : Block := { block with instructions }
                (entry.1, .fn { definition with blocks :=
                  definition.blocks.setIfInBounds 2 replacement }) }

/-- Exact layout identity is a hard gate.  A separately valid same-arity
allocation with another layout is reported and left structurally unchanged;
the validator is run on both sides of that no-op result. -/
def incompatibleLayoutRejected : Bool :=
  match compile unaliasedMain with
  | .error _ => false
  | .ok compiled =>
      let source := incompatibleProgram compiled.baseline.artifact.program
      let baselineContext := compiled.baseline.artifact.validationContext
      let context : Validate.Context :=
        { baselineContext with
          schemas := fun world identity =>
            if world == .shared && identity == otherConsId then
              some { layout := otherConsLayout,
                     fields := #[.shared, .shared] }
            else
              baselineContext.schemas world identity }
      match Reuse.optimize context source with
      | .error _ => false
      | .ok output =>
          output.target == source &&
            output.report ==
              { scannedBlocks := 4
                shapeCandidates := 1
                rewritten := 0
                incompatibleLayouts := 1
                helperBlocks := 0 }

private def relayAddress : Address := Address.replicate 0xda
private def relayFactoryAddress : Address := Address.replicate 0xdb
private def factoryFactoryAddress : Address := Address.replicate 0xdc

/-- Small IxIR₁ adapters around the IxIR₀-derived reversal. Saturating the
relay enters an addressed tail call, followed by reversal's self tail calls.
The two factories add nested over-application before reaching that relay. -/
private def papReturnDeclarations : List (Address × IxIR1.Decl) :=
  [(relayAddress, .fn
      { arity := 2, result := .shared, papSafe := true
        body := .letOp (.call reverseAddress #[.var 1, .var 0])
          (.ret (.var 0)) }),
   (relayFactoryAddress, .fn
      { arity := 1, result := .shared, papSafe := true
        body := .letOp (.papp relayAddress #[.var 0]) (.ret (.var 0)) }),
   (factoryFactoryAddress, .fn
      { arity := 1, result := .shared, papSafe := true
        body := .letOp (.drop (.var 0))
          (.letOp (.papp relayFactoryAddress #[]) (.ret (.var 0))) })]

private def papReturnMain (overApplied aliased : Bool) : IxIR1.Code :=
  let finish := if aliased then
    .letOp (.alloc .shared pairId #[.var 0, .var 3]) (.ret (.var 0))
    else .ret (.var 0)
  let application := if overApplied then
    .letOp (.papp factoryFactoryAddress #[])
      (.letOp (.apply (.var 0)
        #[.erased, .var (if aliased then 6 else 5), .var 1]) finish)
    else
      .letOp (.papp relayAddress #[.var (if aliased then 5 else 4)])
        (.letOp (.apply (.var 0) #[.var 1]) finish)
  .letOp (.alloc .shared nilId #[])
    (.letOp (.alloc .shared nilId #[])
      (.letOp (.alloc .shared consId #[.lit (.nat 3), .var 0])
        (.letOp (.alloc .shared consId #[.lit (.nat 2), .var 0])
          (.letOp (.alloc .shared consId #[.lit (.nat 1), .var 0])
            (if aliased then .letOp (.dup (.var 0)) application
             else application)))))

private def papReturnCompile (overApplied aliased : Bool) : Except CompileError
    (Sigma fun baseline : Lower.Checked =>
      Reuse.Output Validate.defaultLimits baseline.artifact.validationContext
        baseline.artifact.program) := do
  let (declarations, _) ← (IxIR1.Lower.lowerAll sourceDeclarations unaliasedMain
    .shared).mapError CompileError.ixir1
  let context : Lower.Context :=
    { loweringContext with
      parameterWorlds := fun address =>
        if address == relayAddress then some #[.shared, .shared]
        else if address == relayFactoryAddress || address == factoryFactoryAddress
          then some #[.shared]
        else loweringContext.parameterWorlds address }
  let baseline ← (Lower.lowerChecked context
    { declarations := papReturnDeclarations ++ declarations
      main := papReturnMain overApplied aliased
      mainResult := .shared }).mapError CompileError.baseline
  let optimized ← (Reuse.optimize baseline.artifact.validationContext
    baseline.artifact.program).mapError CompileError.reuse
  return ⟨baseline, optimized⟩

/-- A PAP caller survives both kinds of tail call and, optionally, nested
over-application. Every route compares all target interpretations, pins the
PAP ownership overhead, and fully reclaims both the result and any alias. -/
def papTailReturnBenchmark (overApplied aliased : Bool) : Bool :=
  match papReturnCompile overApplied aliased with
  | .error _ => false
  | .ok ⟨baseline, optimized⟩ =>
      let baselineProgram := baseline.artifact.program
      let context := baseline.artifact.validationContext
      let relayTail := match baselineProgram.declarations.find? (fun entry =>
          entry.1 == relayAddress) with
        | some (_, .fn definition) =>
            match definition.blocks[0]? with
            | some block => block.instructions.isEmpty &&
                block.terminator == .tailCall reverseAddress #[.reg 0, .reg 1]
            | none => false
        | _ => false
      relayTail && optimized.report == { expectedReport with scannedBlocks := 7 } &&
        match Eval.runMain (targetContext context baselineProgram)
            .logical baselineProgram 1000 1000,
          Eval.runMain (targetContext context baselineProgram)
            .physical baselineProgram 1000 1000,
          Eval.runMain (targetContext context optimized.target)
            .logical optimized.target 1000 1000,
          Eval.runMain (targetContext context optimized.target)
            .physical optimized.target 1000 1000 with
        | .ok baselineLogical, .ok baselinePhysical, .ok logical, .ok physical =>
            let observed := fun result : Eval.Result =>
              if aliased then targetPair? 100 result.store result.value ==
                some ([3, 2, 1], [1, 2, 3])
              else targetNats? 100 result.store result.value == some [3, 2, 1]
            let papCount := if overApplied then 3 else 1
            let papRCOps := if overApplied then 5 else 3
            observed baselineLogical && observed baselinePhysical &&
              observed logical && observed physical &&
              baselineLogical.store.counters == baselinePhysical.store.counters &&
              baselinePhysical.store.counters.allocs ==
                (if aliased then 9 else 8) + papCount &&
              baselinePhysical.store.counters.frees ==
                (if aliased then 0 else 4) + papCount &&
              baselinePhysical.store.counters.rcops ==
                (if aliased then 8 else 10) + papRCOps &&
              physical.store.counters.allocs ==
                (if aliased then 9 else 5) + papCount &&
              physical.store.counters.frees ==
                (if aliased then 0 else 1) + papCount &&
              physical.store.counters.rcops ==
                (if aliased then 8 else 1) + papRCOps &&
              physical.store.counters.reuses == (if aliased then 0 else 3) &&
              physical.store.counters.hotResets == (if aliased then 0 else 3) &&
              physical.store.counters.coldResets == (if aliased then 3 else 0) &&
              terminalCounterLaw logical physical &&
              released baselineLogical && released baselinePhysical &&
              released logical && released physical
        | _, _, _, _ => false

#guard papTailReturnBenchmark false false
#guard papTailReturnBenchmark false true
#guard papTailReturnBenchmark true false
#guard papTailReturnBenchmark true true
#guard zeroFieldChildBenchmark false
#guard zeroFieldChildBenchmark true
#guard unaliasedBenchmark
#guard aliasedBenchmark
#guard incompatibleLayoutRejected
#guard generalizedShapeAccepted
#guard generalizedDecisionTraceAccepted
#guard lateSourceUseRejected

private def returnedPapAddress : Address := Address.replicate 0xdd
private def terminalFactoryAddress : Address := Address.replicate 0xde

/-- Small hand-written IxIR₁ functions force the two immediate residual
dispatcher outcomes: erased return or a PAP which still needs one argument. -/
private def terminalReturnCompile (underApplied : Bool) : Except CompileError
    (Sigma fun baseline : Lower.Checked =>
      Reuse.Output Validate.defaultLimits baseline.artifact.validationContext
        baseline.artifact.program) := do
  let returnedFunction : IxIR1.FnDef :=
    { arity := 3, result := .shared, papSafe := true
      body := .letOp (.drop (.var 2))
        (.letOp (.drop (.var 2)) (.ret (.var 2))) }
  let factory : IxIR1.FnDef :=
    { arity := 1, result := .shared, papSafe := true
      body := if underApplied then
          .letOp (.papp returnedPapAddress #[.var 0]) (.ret (.var 0))
        else .letOp (.drop (.var 0)) (.ret .erased) }
  let context : Lower.Context :=
    { loweringContext with
      parameterWorlds := fun address =>
        if address == terminalFactoryAddress then some #[.shared]
        else if address == returnedPapAddress then some #[.shared, .shared, .shared]
        else none }
  let baseline ← (Lower.lowerChecked context
    { declarations := [(terminalFactoryAddress, .fn factory),
        (returnedPapAddress, .fn returnedFunction)]
      main := .letOp (.alloc .shared nilId #[])
        (.letOp (.alloc .shared nilId #[])
          (.letOp (.papp terminalFactoryAddress #[])
            (.letOp (.apply (.var 0) #[.var 2, .var 1]) (.ret (.var 0)))))
      mainResult := .shared }).mapError CompileError.baseline
  let optimized ← (Reuse.optimize baseline.artifact.validationContext
    baseline.artifact.program).mapError CompileError.reuse
  return ⟨baseline, optimized⟩

private def terminalReturnObserved (underApplied : Bool) (result : Eval.Result) : Bool :=
  if !underApplied then result.value == .erased
  else match result.value with
    | .loc location => match result.store.get? location with
      | some ⟨.shared, 1, .papN address 3 captured⟩ =>
          address == returnedPapAddress && captured.size == 2 &&
            captured[0]? != captured[1]? && captured.all (fun value =>
              match value with
              | .loc child => match result.store.get? child with
                | some ⟨.shared, 1, .ctorN identity fields⟩ =>
                    identity == nilId && fields.isEmpty
                | _ => false
              | _ => false)
      | _ => false
    | _ => false

/-- Residual application releases every erased argument or retains two
distinct captured owners in an extended PAP. All four interpretations agree
on the result, exact ownership overhead, and complete final reclamation. -/
def immediateApplyMoreBenchmark (underApplied : Bool) : Bool :=
  match terminalReturnCompile underApplied with
  | .error _ => false
  | .ok ⟨baseline, optimized⟩ =>
      let baselineProgram := baseline.artifact.program
      let context := baseline.artifact.validationContext
      match Eval.runMain (targetContext context baselineProgram)
          .logical baselineProgram 100 100,
        Eval.runMain (targetContext context baselineProgram)
          .physical baselineProgram 100 100,
        Eval.runMain (targetContext context optimized.target)
          .logical optimized.target 100 100,
        Eval.runMain (targetContext context optimized.target)
          .physical optimized.target 100 100 with
      | .ok baselineLogical, .ok baselinePhysical, .ok logical, .ok physical =>
          optimized.report.rewritten == 0 &&
            ([baselineLogical, baselinePhysical, logical, physical].all fun result =>
              terminalReturnObserved underApplied result && released result &&
                result.store.counters.allocs == (if underApplied then 5 else 3) &&
                result.store.counters.frees == (if underApplied then 2 else 3) &&
                result.store.counters.rcops == (if underApplied then 4 else 3) &&
                result.store.live == (if underApplied then 3 else 0)) &&
            baselineLogical.store.counters == baselinePhysical.store.counters &&
            terminalCounterLaw logical physical
      | _, _, _, _ => false

/-- The normal selector uses the validated rewrite; constraining the number
of blocks to the baseline's three forces a real target-validation rejection
and executes the unchanged checked baseline with an explicit skip report. -/
def productionSelectionBenchmark (fallback : Bool) : Bool :=
  match compile unaliasedMain with
  | .error _ => false
  | .ok compiled =>
      let source := compiled.baseline.artifact.program
      let context := compiled.baseline.artifact.validationContext
      let limits : Validate.Limits :=
        if fallback then { maxBlocksPerFunction := 3 } else Validate.defaultLimits
      match Reuse.selectWith limits context source with
      | .error _ => false
      | .ok selected =>
          let expected : Reuse.SelectionReport := if fallback then
            .skipped (.limit { owner := .declaration reverseAddress, block := 0 }
              .blocksPerFunction 5 3)
            else .applied expectedReport
          selected.report == expected &&
            selected.target == (if fallback then source else compiled.optimized.target) &&
            match Eval.runMain (targetContext context selected.target)
                .physical selected.target 1000 1000 with
            | .error _ => false
            | .ok result =>
                targetNats? 100 result.store result.value == some [3, 2, 1] &&
                  result.store.counters.allocs == (if fallback then 8 else 5) &&
                  result.store.counters.reuses == (if fallback then 0 else 3) &&
                  released result

/-- The production selector never turns rejected source input into a
successful baseline selection. -/
def productionSelectionRejectsSource : Bool :=
  match compile unaliasedMain with
  | .error _ => false
  | .ok compiled =>
      match Reuse.selectWith { maxBlocksPerFunction := 0 }
          compiled.baseline.artifact.validationContext
          compiled.baseline.artifact.program with
      | .error (.invalidSource error) =>
          error == .limit { owner := .declaration reverseAddress, block := 0 }
            .blocksPerFunction 3 0
      | _ => false

#guard immediateApplyMoreBenchmark false
#guard immediateApplyMoreBenchmark true
#guard productionSelectionBenchmark false
#guard productionSelectionBenchmark true
#guard productionSelectionRejectsSource


/-- Proof-carrying result of an ordinary executable benchmark check. -/
structure CheckedBenchmark (benchmark : Bool) : Type where
  accepted : benchmark = true

def checkBenchmark (name : String) (benchmark : Bool) :
    Except String (CheckedBenchmark benchmark) :=
  if accepted : benchmark = true then
    .ok { accepted }
  else
    .error s!"{name} failed"

def checkUnaliased : Except String (CheckedBenchmark unaliasedBenchmark) :=
  checkBenchmark "all-hot compiler-emitted reversal" unaliasedBenchmark

def checkAliased : Except String (CheckedBenchmark aliasedBenchmark) :=
  checkBenchmark "all-cold compiler-emitted reversal" aliasedBenchmark

def checkPapTailReturn (overApplied aliased : Bool) :
    Except String (CheckedBenchmark (papTailReturnBenchmark overApplied aliased)) :=
  checkBenchmark
    s!"PAP return through addressed/self tail calls (over={overApplied}, alias={aliased})"
    (papTailReturnBenchmark overApplied aliased)

def checkImmediateApplyMore (underApplied : Bool) :
    Except String (CheckedBenchmark (immediateApplyMoreBenchmark underApplied)) :=
  checkBenchmark s!"immediate residual application (under={underApplied})"
    (immediateApplyMoreBenchmark underApplied)

def checkProductionSelection (fallback : Bool) :
    Except String (CheckedBenchmark (productionSelectionBenchmark fallback)) :=
  checkBenchmark s!"production reuse selection (fallback={fallback})"
    (productionSelectionBenchmark fallback)

def checkProductionSourceRejection :
    Except String (CheckedBenchmark productionSelectionRejectsSource) :=
  checkBenchmark "production reuse preserves source rejection" productionSelectionRejectsSource

def checkZeroFieldChild (aliased : Bool) :
    Except String (CheckedBenchmark (zeroFieldChildBenchmark aliased)) :=
  checkBenchmark (if aliased then "cold reuse after an empty constructor prologue"
    else "hot reuse after an empty constructor prologue")
    (zeroFieldChildBenchmark aliased)

def checkIncompatibleLayout :
    Except String (CheckedBenchmark incompatibleLayoutRejected) :=
  checkBenchmark "incompatible-layout rejection" incompatibleLayoutRejected

def checkGeneralizedShape :
    Except String (CheckedBenchmark generalizedShapeAccepted) :=
  checkBenchmark "generalized checked-liveness reuse shape"
    generalizedShapeAccepted

def checkLateSourceUse :
    Except String (CheckedBenchmark lateSourceUseRejected) :=
  checkBenchmark "post-release source-use rejection" lateSourceUseRejected

end Ix.Compiler.IxIR2.Reuse.Examples
