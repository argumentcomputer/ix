import CompilatrixTests.Support
import CompilatrixTests.Addressing.Fixtures
import Compilatrix.IxIR2.Pipeline

namespace CompilatrixTests

open Compilatrix.Ixon

namespace IxIR2PipelineFixtures

open Compilatrix
open Compilatrix.Ixon

def constructorBlockA : Address := Address.replicate 0xb1
def constructorBlockB : Address := Address.replicate 0xb2

def constructorA : IxIR2.CtorId :=
  { block := constructorBlockA, indIdx := 0, cidx := 0 }

def constructorB : IxIR2.CtorId :=
  { block := constructorBlockB, indIdx := 0, cidx := 0 }

def ambiguousInput : IxIR2.Lower.Input :=
  { declarations := []
    main :=
      .letOp (.alloc .shared constructorA #[.lit (.nat 9)])
        (.letOp (.fetch (.var 0) 0) (.ret (.var 1)))
    mainResult := .shared }

def ambiguousSidecars : IxIR2.Pipeline.Sidecars :=
  { input := ambiguousInput
    parameterEntries := []
    constructors :=
      [{ identity := constructorA, arity := 1 },
       { identity := constructorB, arity := 1 }] }

/-- Global constructor ambiguity no longer blocks a projection whose lexical
producer is an exact local allocation. -/
def ambiguousFetchAcceptedByProducerFact : Bool :=
  match IxIR2.Lower.lowerChecked ambiguousSidecars.context ambiguousInput with
  | .error _ => false
  | .ok checked =>
      let context := IxIR2.Eval.Context.ofProgram checked.artifact.program
        checked.artifact.validationContext.schemas
      checked.artifact.trace.fetchCapabilitiesMatch &&
        ambiguousSidecars.traceExactFetchesMatch checked.artifact.trace &&
        match IxIR2.Eval.runMain context .logical checked.artifact.program 8 2 with
        | .ok result =>
            match result.value with
            | .loc _ => result.store.live == 1
            | _ => false
        | .error _ => false

def ambiguousCaseInput : IxIR2.Lower.Input :=
  { declarations := []
    main :=
      .letOp (.alloc .shared constructorA #[.lit (.nat 9)])
        (.case (.var 0) false
          #[.mk 0 1
            (.letOp (.drop (.var 1)) (.ret (.lit (.nat 9))))])
    mainResult := .shared }

def ambiguousCaseSidecars : IxIR2.Pipeline.Sidecars :=
  { ambiguousSidecars with input := ambiguousCaseInput }

/-- Exact path-local HPT provenance also disambiguates a constructor switch.
The independent trace check certifies that the selected identity occurs in
the emitted terminator, and execution takes that branch successfully. -/
def ambiguousCaseAcceptedByProducerFact : Bool :=
  match IxIR2.Lower.lowerChecked ambiguousCaseSidecars.context
      ambiguousCaseInput with
  | .error _ => false
  | .ok checked =>
      let context := IxIR2.Eval.Context.ofProgram checked.artifact.program
        checked.artifact.validationContext.schemas
      ambiguousCaseSidecars.traceExactCaseTargetsMatch
          checked.artifact.trace &&
        match IxIR2.Eval.runMain context .logical checked.artifact.program 16 4 with
        | .ok result =>
            result.value == .lit (.nat 9) && result.store.live == 0
        | .error _ => false

def unresolvedFetcher : Address := Address.replicate 0xba

def unresolvedFetchInput : IxIR2.Lower.Input :=
  { declarations :=
      [(unresolvedFetcher,
        .fn
          { arity := 1
            result := .shared
            papSafe := true
            body :=
              .letOp (.fetch (.var 0) 0) (.ret (.var 0)) })]
    main :=
      .letOp (.alloc .shared constructorA #[.lit (.nat 9)])
        (.letOp (.call unresolvedFetcher #[.var 0]) (.ret (.var 0)))
    mainResult := .shared }

def unresolvedFetchSidecars : IxIR2.Pipeline.Sidecars :=
  { input := unresolvedFetchInput
    parameterEntries := [(unresolvedFetcher, #[.shared])]
    constructors :=
      [{ identity := constructorA, arity := 1 },
       { identity := constructorB, arity := 1 }] }

/-- An unrefined function parameter remains ambiguous and fails closed. -/
def unresolvedFetchRejected : Bool :=
  match IxIR2.Lower.lowerChecked unresolvedFetchSidecars.context
      unresolvedFetchInput with
  | .error (.schema _ _) => true
  | _ => false

def scalarConstructorA : IxIR2.CtorId :=
  { block := Address.replicate 0xbb, indIdx := 0, cidx := 0 }

def scalarConstructorB : IxIR2.CtorId :=
  { block := Address.replicate 0xbc, indIdx := 0, cidx := 0 }

def ambiguousScalarFreeInput : IxIR2.Lower.Input :=
  { declarations := []
    main :=
      .letOp (.alloc .unique scalarConstructorA #[])
        (.letOp (.free (.var 0)) (.ret (.lit (.nat 4))))
    mainResult := .shared }

def ambiguousScalarFreeSidecars : IxIR2.Pipeline.Sidecars :=
  { input := ambiguousScalarFreeInput
    parameterEntries := []
    constructors :=
      [{ identity := scalarConstructorA, arity := 0 },
       { identity := scalarConstructorB, arity := 0 }] }

/-- The same exact-producer rule disambiguates a shallow unique free and the
logical machine observes an empty live heap afterward. -/
def ambiguousScalarFreeAcceptedByProducerFact : Bool :=
  match IxIR2.Lower.lowerChecked ambiguousScalarFreeSidecars.context
      ambiguousScalarFreeInput with
  | .error _ => false
  | .ok checked =>
      let context := IxIR2.Eval.Context.ofProgram checked.artifact.program
        checked.artifact.validationContext.schemas
      ambiguousScalarFreeSidecars.traceScalarLeavesMatch
          checked.artifact.trace &&
        match IxIR2.Eval.runMain context .logical checked.artifact.program 8 2 with
        | .ok result =>
            result.value == .lit (.nat 4) && result.store.live == 0
        | .error _ => false

def pappTarget : Address := Address.replicate 0xbd

def pappInput : IxIR2.Lower.Input :=
  { declarations :=
      [(pappTarget,
        .fn
          { arity := 2
            result := .shared
            papSafe := true
            body :=
              .letOp (.drop (.var 0))
                (.letOp (.drop (.var 2)) (.ret (.lit (.nat 0)))) })]
    main :=
      .letOp (.papp pappTarget #[.lit (.nat 7)]) (.ret (.var 0))
    mainResult := .shared }

def pappSidecars : IxIR2.Pipeline.Sidecars :=
  { input := pappInput
    parameterEntries := [(pappTarget, #[.shared, .shared])]
    constructors := [] }

/-- Checked function-PAP lowering records the exact shared capture transition
and the logical machine retains precisely the fresh PAP owner. -/
def pappCapabilityTransitionAccepted : Bool :=
  match IxIR2.Lower.lowerChecked pappSidecars.context pappInput with
  | .error _ => false
  | .ok checked =>
      let emittedPapp :=
        match checked.artifact.program.main.blocks[0]? with
        | some block =>
            block.instructions[0]? ==
              some (.papp pappTarget #[.lit (.nat 7)])
        | none => false
      let context := IxIR2.Eval.Context.ofProgram checked.artifact.program
        checked.artifact.validationContext.schemas
      emittedPapp &&
        pappSidecars.tracePappsSafe checked.artifact.trace &&
        checked.artifact.trace.allocationCapabilitiesMatch &&
        match IxIR2.Eval.runMain context .logical checked.artifact.program 4 1 with
        | .ok result =>
            match result.value with
            | .loc location =>
                result.store.live == 1 &&
                  match result.store.get? location with
                  | some box =>
                      box.world == .shared && box.rc == 1 &&
                        match box.node with
                        | .papN address arity arguments =>
                            address == pappTarget && arity == 2 &&
                              arguments == #[.lit (.nat 7)]
                        | _ => false
                  | none => false
            | _ => false
        | .error _ => false

def unsafePappInput : IxIR2.Lower.Input :=
  { pappInput with
    declarations :=
      [(pappTarget,
        .fn
          { arity := 2
            result := .shared
            papSafe := false
            body :=
              .letOp (.drop (.var 0))
                (.letOp (.drop (.var 2)) (.ret (.lit (.nat 0)))) })] }

def unsafePappSidecars : IxIR2.Pipeline.Sidecars :=
  { pappSidecars with input := unsafePappInput }

/-- The attachment-side trace check fails closed if the exact declaration
environment no longer marks a retained `papp` target safe. -/
def pappSafetyCheckRejectsUnsafe : Bool :=
  match IxIR2.Lower.lowerChecked pappSidecars.context pappInput with
  | .error _ => false
  | .ok checked =>
      !unsafePappSidecars.tracePappsSafe checked.artifact.trace

def retiredBorrowInput : IxIR2.Lower.Input :=
  { declarations := []
    main :=
      .letOp (.alloc .shared constructorA #[.lit (.nat 9)])
        (.letOp (.fetch (.var 0) 0)
          (.letOp (.drop (.var 1)) (.ret (.lit (.nat 4)))))
    mainResult := .shared }

def retiredBorrowSidecars : IxIR2.Pipeline.Sidecars :=
  { input := retiredBorrowInput
    parameterEntries := []
    constructors := [{ identity := constructorA, arity := 1 }] }

/-- Consuming an owner after its loan's final use retires both the owner and
the validator-dead borrow in the producer continuation. -/
def lenderDestructionRetiresBorrow : Bool :=
  match IxIR2.Lower.lowerChecked retiredBorrowSidecars.context
      retiredBorrowInput with
  | .error _ => false
  | .ok checked =>
      let retired := checked.artifact.trace.positions.any fun position =>
        position.source.owner == IxIR2.Validate.Owner.main &&
          position.source.offset == 3 &&
          position.sourceCapabilities ==
            #[.scalar, .dead, .dead]
      let context := IxIR2.Eval.Context.ofProgram checked.artifact.program
        checked.artifact.validationContext.schemas
      checked.artifact.trace.destructionCapabilitiesMatch && retired &&
        match IxIR2.Eval.runMain context .logical checked.artifact.program 6 2 with
        | .ok result =>
            result.value == .lit (.nat 4) && result.store.live == 0
        | .error _ => false

def recursorOwner : Address := Address.replicate 0xb3
def recursorGroupA : Address := Address.replicate 0xb4
def recursorGroupB : Address := Address.replicate 0xb5

def caseConstructorA : IxIR2.CtorId :=
  { block := Address.replicate 0xb6, indIdx := 0, cidx := 0 }

def caseConstructorB : IxIR2.CtorId :=
  { block := Address.replicate 0xb7, indIdx := 0, cidx := 0 }

def exactRecursorInput : IxIR2.Lower.Input :=
  { declarations :=
      [(recursorOwner,
        .fn
          { arity := 1
            result := .shared
            papSafe := true
            body :=
              .case (.var 0) false #[
                .mk 0 0
                  (.letOp (.drop (.var 0))
                    (.ret (.lit (.nat 3))))] })]
    main :=
      .letOp (.alloc .shared caseConstructorA #[])
        (.letOp (.call recursorOwner #[.var 0]) (.ret (.var 0)))
    mainResult := .shared }

def residualRecursorInput : IxIR2.Lower.Input :=
  { exactRecursorInput with
    main :=
      .letOp (.alloc .shared caseConstructorB #[])
        (.letOp (.call recursorOwner #[.var 0]) (.ret (.var 0))) }

def exactRecursorSidecars : IxIR2.Pipeline.Sidecars :=
  { input := exactRecursorInput
    parameterEntries := [(recursorOwner, #[.shared])]
    constructors :=
      [{ identity := caseConstructorA
         arity := 0
         group := some recursorGroupA },
       { identity := caseConstructorB
         arity := 0
         group := some recursorGroupB }]
    recursorOrigins :=
      [{ owner := recursorOwner, group := recursorGroupA }] }

/-- A recursor parameter whose HPT fact remains ambiguous is lowered with
both producer-known full identities sharing its erased tag/arity.  Executing
the same checked branch with either constructor demonstrates that residual
coverage no longer guesses one mutual-block identity. -/
def exactRecursorCaseAccepted : Bool :=
  let accepts := fun input =>
    let sidecars := { exactRecursorSidecars with input := input }
    match IxIR2.Lower.lowerChecked sidecars.context input with
    | .error _ => false
    | .ok checked =>
        let declaration := checked.artifact.program.declarations.find? fun entry =>
          entry.1 == recursorOwner
        let coveredSwitch := match declaration with
          | some (_, .fn definition) =>
              match definition.blocks[0]? with
              | some block =>
                  match block.terminator with
                  | .switchValue _ constructors _ =>
                      constructors.size == 2 &&
                        constructors.any (fun target =>
                          target.cid == caseConstructorA) &&
                        constructors.any (fun target =>
                          target.cid == caseConstructorB)
                  | _ => false
              | none => false
          | _ => false
        let context := IxIR2.Eval.Context.ofProgram checked.artifact.program
          checked.artifact.validationContext.schemas
        coveredSwitch &&
          sidecars.traceResidualCaseTargetsMatch checked.artifact.trace &&
          sidecars.traceConstructorsKnown checked.artifact.trace &&
          match IxIR2.Eval.runMain context .logical checked.artifact.program
              8 2 with
          | .ok result =>
              result.value == .lit (.nat 3) && result.store.live == 0
          | .error _ => false
  accepts exactRecursorInput && accepts residualRecursorInput

def recursorSourceA : Address := Address.replicate 0xb8
def recursorSourceB : Address := Address.replicate 0xb9

def sourceRecursor : IxIR0.Decl :=
  .recursor 0 false #[{ fields := 0, rhs := .lit (.nat 3) }]

def sourceRecursorFn : IxIR1.Decl :=
  .fn
    { arity := 1
      result := .shared
      papSafe := true
      body :=
        .case (.var 0) false #[
          .mk 0 0
            (.letOp (.drop (.var 0)) (.ret (.lit (.nat 3))))] }

def originBlock (group source constructor : Address) :
    IxIR0.MutualBlock.Result :=
  { blockAddress := group
    blockMembers := []
    members := [(source, sourceRecursor), (constructor, .ctor 0 0)]
    addressMap := [] }

/-- The production extractor follows the complete final owner map, and rejects
two distinct mutual-block origins collapsed onto one IxIR₁ identity. -/
def recursorOriginExtractionOk : Bool :=
  let sourceA :=
    [(recursorSourceA, sourceRecursor),
     (caseConstructorA.block, IxIR0.Decl.ctor 0 0)]
  let blockA := originBlock recursorGroupA recursorSourceA
    caseConstructorA.block
  let exact := IxIR2.Pipeline.deriveRecursorOrigins sourceA [blockA]
    [(recursorSourceA, sourceRecursorFn)]
    [(recursorSourceA, recursorOwner)]
  let sourceBoth := sourceA ++
    [(recursorSourceB, sourceRecursor),
     (caseConstructorB.block, IxIR0.Decl.ctor 0 0)]
  let blockB := originBlock recursorGroupB recursorSourceB
    caseConstructorB.block
  let conflict := IxIR2.Pipeline.deriveRecursorOrigins sourceBoth
    [blockA, blockB]
    [(recursorSourceA, sourceRecursorFn),
     (recursorSourceB, sourceRecursorFn)]
    [(recursorSourceA, recursorOwner),
     (recursorSourceB, recursorOwner)]
  let exactOk := match exact with
    | .ok [origin] =>
        origin.owner == recursorOwner && origin.group == recursorGroupA
    | _ => false
  exactOk &&
    match conflict with
    | .error (.recursorOriginConflict owner) => owner == recursorOwner
    | _ => false

end IxIR2PipelineFixtures

end CompilatrixTests
