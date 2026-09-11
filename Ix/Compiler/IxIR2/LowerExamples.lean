import Ix.Compiler.IxIR1.Eval
import Ix.Compiler.IxIR2.Eval
import Ix.Compiler.IxIR2.Lower

/-!
# Executable structured-lowering witnesses

These fixtures exercise producer-generated block parameters rather than
hand-written IxIR₂. They require `lowerChecked`, inspect its CFG/trace, and
compare successful IxIR₁ execution with logical IxIR₂ execution.
-/

namespace Ix.Compiler.IxIR2.Lower.Examples

open Ix.Compiler.Ixon (Address Owned)
open Ix.Compiler.IxIR2

private def natAddress : Address := Address.replicate 0x71
private def inspectAddress : Address := Address.replicate 0x72
private def blockAddress : Address := Address.replicate 0x73
private def nilLayout : LayoutId := Address.replicate 0x74
private def consLayout : LayoutId := Address.replicate 0x75

private def nilCtor : CtorId :=
  { block := blockAddress, indIdx := 0, cidx := 0 }

private def consCtor : CtorId :=
  { block := blockAddress, indIdx := 0, cidx := 1 }

private def schemas : Owned → CtorId → Option CtorSchema
  | .shared, cid =>
      if cid == nilCtor then
        some { layout := nilLayout, fields := #[] }
      else if cid == consCtor then
        some { layout := consLayout, fields := #[.shared] }
      else
        none
  | .unique, cid =>
      if cid == nilCtor then
        some { layout := nilLayout, fields := #[] }
      else
        none

private def sourceContext (input : Input) : IxIR1.Ctx :=
  { decls := IxIR1.Env.ofList input.declarations }

private def targetFunction? (artifact : Artifact) (address : Address) :
    Option Function :=
  let declaration : Option Decl :=
    (artifact.program.declarations.find?
      fun entry => entry.1 == address).map (fun entry => entry.2)
  match declaration with
  | some (Decl.fn definition) => some definition
  | _ => none

private def targetRun (artifact : Artifact) (controlFuel heapFuel : Nat) :=
  Eval.runMain
    (Eval.Context.ofProgram artifact.program artifact.validationContext.schemas)
    .logical artifact.program controlFuel heapFuel

/-! ## Literal-Nat case and tail transfer -/

private def natBody : IxIR1.Code :=
  .case (.var 0) true #[
    .mk 0 0
      (.letOp (.drop (.var 0)) (.ret (.lit (.nat 1)))),
    .mk 1 1
      (.letOp (.drop (.var 1)) (.ret (.lit (.nat 0))))]

private def natInput : Input :=
  { declarations :=
      [(natAddress,
        .fn { arity := 1, result := .shared, papSafe := true, body := natBody })]
    main :=
      .letOp (.call natAddress #[.lit (.nat 7)]) (.ret (.var 0))
    mainResult := .shared }

private def natContext : Context :=
  { parameterWorlds := fun address =>
      if address == natAddress then some #[.shared] else none
    schemas }

private def loweredNat := lowerChecked natContext natInput

#guard match loweredNat with
  | .ok checked =>
      checked.stats.functions == 2 && checked.stats.blocks == 4 &&
        checked.stats.edges == 2 && checked.artifact.trace.edges.length == 2 &&
        functionTraceMatches checked.artifact.mainTrace .main
          natInput.mainDefinition checked.artifact.program.main &&
        (match checked.artifact.trace.functions with
        | [natTrace, mainTrace] =>
            natTrace.owner == Validate.Owner.declaration natAddress &&
              mainTrace.owner == Validate.Owner.main &&
              functionSourceMatches natTrace.source natTrace.generated
                natTrace.root &&
              functionSourceMatches mainTrace.source mainTrace.generated
                mainTrace.root &&
              natTrace.source.arity == 1 &&
              natTrace.source.result == .shared &&
              natTrace.source.papSafe &&
              mainTrace.source.arity == 0 &&
              mainTrace.source.result == .shared &&
              !mainTrace.source.papSafe &&
              (match natTrace.source.body with
              | .case (.var 0) true alternatives => alternatives.size == 2
              | _ => false) &&
              (match mainTrace.source.body with
              | .letOp (.call address arguments) (.ret (.var 0)) =>
                  address == natAddress && arguments == #[.lit (.nat 7)]
              | _ => false) &&
              natTrace.root.blocks.length == 3 &&
              mainTrace.root.blocks.length == 1 &&
              natTrace.root.switchBranchesMatch &&
              mainTrace.root.switchBranchesMatch &&
              match natTrace.root, mainTrace.root with
              | .switchValue _ 0 inputMap 1 _ _ _ _ generated outgoing children,
                  .tailCall _ 0 mainMap 0 _ _ mainGenerated =>
                  inputMap == #[some (.reg 0)] && mainMap.isEmpty &&
                    outgoing.length == 2 && children.length == 2 &&
                    natTrace.generated.blocks[0]? == some generated &&
                    mainTrace.generated.blocks[0]? == some mainGenerated
              | _, _ => false
        | _ => false) &&
        (match checked.artifact.trace.edges with
        | [zero, succ] =>
            zero.sourceInputMap == #[some (.reg 0)] &&
              zero.sourceMap == #[some (.reg 0)] &&
              zero.explicitValues == #[.reg 0] &&
              zero.implicitScalars == 0 &&
              succ.sourceInputMap == #[some (.reg 0)] &&
              succ.sourceMap == #[some (.reg 0), some (.reg 1)] &&
              succ.explicitValues == #[.reg 0] &&
              succ.implicitScalars == 1
        | _ => false) &&
        match targetFunction? checked.artifact natAddress with
        | some definition =>
            definition.blocks.size == 3 &&
              match checked.artifact.program.main.blocks[0]? with
              | some block =>
                  match block.terminator with
                  | .tailCall address arguments =>
                      address == natAddress && arguments == #[.lit (.nat 7)]
                  | _ => false
              | _ => false
        | none => false
  | .error _ => false

#guard match IxIR1.runMain (sourceContext natInput) natInput.main 20, loweredNat with
  | .ok source, .ok checked =>
      match targetRun checked.artifact 4 1 with
      | .ok target =>
          source.2 == target.value && target.value == .lit (.nat 0) &&
            source.1.live == 0 && target.store.live == 0 &&
            target.controlRemaining == 0 && target.heapRemaining == 0
      | .error _ => false
  | _, _ => false

/-! ## Constructor dispatch, fetched field, and explicit join environments -/

private def inspectBody : IxIR1.Code :=
  .case (.var 0) false #[
    .mk 0 0
      (.letOp (.drop (.var 0)) (.ret (.lit (.nat 0)))),
    .mk 1 1
      (.letOp (.dup (.var 0))
        (.letOp (.drop (.var 2)) (.ret (.var 1))))]

private def constructorInput : Input :=
  { declarations :=
      [(inspectAddress,
        .fn
          { arity := 1
            result := .shared
            papSafe := true
            body := inspectBody })]
    main :=
      .letOp (.alloc .shared nilCtor #[])
        (.letOp (.alloc .shared consCtor #[.var 0])
          (.letOp (.call inspectAddress #[.var 0]) (.ret (.var 0))))
    mainResult := .shared }

private def constructorContext : Context :=
  { parameterWorlds := fun address =>
      if address == inspectAddress then some #[.shared] else none
    schemas
    caseCtors := fun site alternative =>
      if site.owner == Validate.Owner.declaration inspectAddress &&
          site.branches.isEmpty && site.offset == 0 then
        if alternative == 0 then [nilCtor]
        else if alternative == 1 then [consCtor]
        else []
      else
        [] }

private def loweredConstructor := lowerChecked constructorContext constructorInput

#guard match loweredConstructor with
  | .ok checked =>
        checked.stats.blocks == 4 && checked.stats.edges == 2 &&
        checked.artifact.trace.edges.length == 2 &&
        checked.artifact.trace.positionsMatch &&
        checked.artifact.trace.pureCapabilitiesMatch &&
        checked.artifact.trace.dupCapabilitiesMatch &&
        checked.artifact.trace.fetchCapabilitiesMatch &&
        checked.artifact.trace.allocationCapabilitiesMatch &&
        checked.artifact.trace.positions.any fun position =>
          position.source.owner == Validate.Owner.main &&
            position.source.branches.isEmpty &&
            position.source.offset == 1 && position.block == 0 &&
            position.target == .instruction 1 &&
            position.sourceCapabilities == #[.owned .shared] &&
        match targetFunction? checked.artifact inspectAddress with
        | some definition =>
            definition.blocks.size == 3 &&
              definition.blocks[2]!.instructions[0]? ==
                some (.fetch (.reg 0) consCtor 0)
        | none => false
  | .error _ => false

private def returnedCtorIxIR1 (out : IxIR1.Store × IxIR1.RVal) :
    Option CtorId :=
  match out.2 with
  | .loc location =>
      match out.1.get? location with
      | some { node := .ctorN cid _, .. } => some cid
      | _ => none
  | _ => none

private def returnedCtorIxIR2 (out : Eval.Result) : Option CtorId :=
  match out.value with
  | .loc location =>
      match out.store.get? location with
      | some { node := .ctorN cid _, .. } => some cid
      | _ => none
  | _ => none

#guard match
    IxIR1.runMain (sourceContext constructorInput) constructorInput.main 50,
    loweredConstructor with
  | .ok source, .ok checked =>
      match targetRun checked.artifact 8 2 with
      | .ok target =>
          returnedCtorIxIR1 source == some nilCtor &&
            returnedCtorIxIR2 target == some nilCtor &&
            source.1.live == 1 && target.store.live == 1 &&
            source.1.allocs == target.store.counters.allocs &&
            source.1.frees == target.store.counters.frees &&
            source.1.rcops == target.store.counters.rcops &&
            target.controlRemaining == 0 && target.heapRemaining == 0
      | .error _ => false
  | _, _ => false

/-! ## Owner-sensitive scalar-leaf facts -/

private def freeInput : Input :=
  { declarations := []
    main :=
      .letOp (.alloc .unique nilCtor #[])
        (.letOp (.free (.var 0)) (.ret .erased))
    mainResult := .shared }

private def freeContext : Context :=
  { schemas
    scalarFreeCtor := fun site =>
      if site.owner == Validate.Owner.main && site.branches.isEmpty &&
          site.offset == 1 then some nilCtor else none }

#guard match lowerChecked freeContext freeInput with
  | .ok checked =>
      checked.artifact.validationContext.scalarLeaves ==
        [{ owner := .main, block := 0, value := 0, cid := nilCtor }] &&
        match targetRun checked.artifact 3 0 with
        | .ok target =>
            target.value == .erased && target.store.live == 0 &&
              target.store.counters.allocs == 1 &&
              target.store.counters.frees == 1
        | .error _ => false
  | .error _ => false

/-! ## Dead ownership slots at CFG edges -/

/-- `pure` moves the only owner into a new source binder. The older runtime
slot still contains the same location in IxIR₁, but it is dead and must not
be related to the successor's deliberately erased block parameter. -/
private def deadEdgeInput : Input :=
  { declarations := []
    main :=
      .letOp (.alloc .shared nilCtor #[])
        (.letOp (.pure (.var 0))
          (.case (.var 0) false #[
            .mk 0 0
              (.letOp (.drop (.var 0)) (.ret (.lit (.nat 9))))]))
    mainResult := .shared }

private def deadEdgeContext : Context :=
  { schemas
    caseCtors := fun site alternative =>
      if site.owner == Validate.Owner.main && site.branches.isEmpty &&
          site.offset == 2 && alternative == 0 then
        [nilCtor]
      else
        [] }

private def loweredDeadEdge := lowerChecked deadEdgeContext deadEdgeInput

#guard match loweredDeadEdge with
  | .ok checked =>
      match checked.artifact.trace.edges with
      | [edge] =>
          edge.sourceInputMap == #[some (.reg 1), none] &&
            edge.sourceMap == #[some (.reg 0), none] &&
            edge.explicitValues == #[.reg 1, .erased] &&
            edge.targetParams == #[.owned .shared, .scalar] &&
            edge.implicitScalars == 0
      | _ => false
  | .error _ => false

#guard match
    IxIR1.runMain (sourceContext deadEdgeInput) deadEdgeInput.main 20,
    loweredDeadEdge with
  | .ok source, .ok checked =>
      match targetRun checked.artifact 5 10 with
      | .ok target =>
          source.2 == .lit (.nat 9) && target.value == source.2 &&
            source.1.live == 0 && target.store.live == 0 &&
            target.controlRemaining == 0
      | .error _ => false
  | _, _ => false

/-! ## Fail-closed source boundaries -/

private def reuseInput : Input :=
  { declarations := []
    main :=
      .letOp (.alloc .unique nilCtor #[])
        (.letOp (.reuse (.var 0) nilCtor #[]) (.ret (.var 0)))
    mainResult := .unique }

#guard match lowerChecked freeContext reuseInput with
  | .error (.unsupported { owner := .main, branches := [], offset := 1 }
      "raw IxIR₁ reuse is outside the baseline subset") => true
  | _ => false

private def missingWorlds : Context := { schemas }

#guard match lowerChecked missingWorlds natInput with
  | .error (.missingParameterWorlds address) => address == natAddress
  | _ => false

end Ix.Compiler.IxIR2.Lower.Examples
