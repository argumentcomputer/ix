import Ix.Compiler.UniqueReuse.Observations

namespace Ix.Compiler.UniqueReuse.Examples

open Lean Ix.Compiler.Ixon

private def rejected (value : Except ε α) : Bool := value.toOption.isNone

private def replace (entries : List (Address × IxIR0.Decl)) (address : Address) (value : IxIR0.Decl) :=
  entries.map fun entry => if entry.1 == address then (address, value) else entry

private def ruleBody (replace : Ixon.Expr → Ixon.Expr) : Ixon.Expr → Ixon.Expr
  | .lam mode domain rest => .lam mode domain (ruleBody replace rest)
  | body => replace body

def rejectionChecks : Except String (List String) := do
  let source ← Examples.source [1, 2, 3]
  let compiled ← (compile source.constants source.entry source.config).mapError reprStr
  let plan := compiled.plan
  let schema := plan.schema
  let recovery := compiled.lowered.checked.recovery
  let .translated target := compiled.backend | throw "rejection fixture has no target"
  let resolve := (Pipeline.ResolverIndex.ofList source.constants).resolve
  let some block := resolve source.dataBlock | throw "rejection fixture has no data block"
  let .muts members := block.info | throw "rejection fixture data block is not mutual"
  let some (.recr recursor) := (members[2]? : Option Ixon.MutConst) | throw "rejection fixture has no recursor"
  let some consRule := recursor.rules[1]? | throw "rejection fixture has no cons rule"
  let mut names := []
  need (rejected (UsageCheck.checkConstant resolve block) &&
    !rejected (RecursorUsage.checkConstant resolve block)) "unique recursor did not cross the explicit usage policy"
  names := names ++ ["v0-remains-conservative", "v1-source-modes-accepted"]
  for (name, changed) in [
      ("indexed-recursor", { recursor with indices := 1 }),
      ("motive-recursor", { recursor with motives := 1 }),
      ("k-recursor", { recursor with k := true }),
      ("recursor-telescope-arity", { recursor with minors := 1 }),
      ("rule-field-count", { recursor with rules := recursor.rules.set! 1 { consRule with fields := 1 } })] do
    need (rejected (RecursorUsage.checkConstant resolve { block with info := .muts (members.set! 2 (.recr changed)) }))
      s!"{name}: source mode checker accepted"
    names := names ++ [name]
  for (name, body) in [
      ("rule-drops-fields", ruleBody (fun _ => .var 2) consRule.rhs),
      ("rule-duplicates-accumulator", ruleBody (fun body => match body with
        | .app fn _ => .app fn (.var 2) | _ => body) consRule.rhs),
      ("rule-partial-call", ruleBody (fun _ => .app (.var 3) (.var 1)) consRule.rhs),
      ("rule-escaping-lambda", ruleBody (fun body => .lam .linear (.sort 0) body) consRule.rhs),
      ("rule-unknown-callable", ruleBody (fun _ => .app (.var 0) (.var 1)) consRule.rhs)] do
    let changed := { recursor with rules := recursor.rules.set! 1 { consRule with rhs := body } }
    need (rejected (RecursorUsage.checkConstant resolve { block with info := .muts (members.set! 2 (.recr changed)) }))
      s!"{name}: source rule checker accepted"
    names := names ++ [name]
  let inst := IxIR0.UniqueReverse.sourceInstance
  for (name, changed) in [
      ("argument-mode-identity", { inst with arguments := [.unique, .unique, .unique] }),
      ("major-mode-identity", { inst with arguments := [.shared, .unique, .shared] }),
      ("head-mode-identity", { inst with fields := [[], [.shared, .unique]] }),
      ("tail-mode-identity", { inst with fields := [[], [.unique, .shared]] }),
      ("result-mode-identity", { inst with result := .shared })] do
    need (changed.wellShaped && changed.bytes != inst.bytes && changed.address != inst.address)
      s!"{name}: canonical instance lost a mode"
    names := names ++ [name]
  need (!({ inst with arguments := [.unique] }).wellShaped &&
    !({ inst with fields := [[], [.unique]] }).wellShaped) "malformed mode vectors accepted"
  names := names ++ ["mode-vector-arity"]
  let entries := compiled.source.erasure.result.raw
  for (name, changed) in [
      ("raw-wrong-builder", replace entries schema.builder (.defn .unique (.lam .linear (.lam .linear (.var 0))))),
      ("raw-wrong-recursor", replace entries schema.recursor (.recursor 2 true #[])),
      ("raw-wrong-cons-arity", replace entries schema.cons (.ctor 1 1)),
      ("raw-wrong-nil-tag", replace entries schema.nil (.ctor 1 0)),
      ("raw-wrong-alias", replace entries schema.alias (.defn .unique (.ref schema.recursor))),
      ("raw-wrong-entry", replace entries recovery.checked.root (.defn .unique .erased))] do
    need ((IxIR0.UniqueReverse.check changed compiled.source.rawMain plan).isNone &&
      (IxIR0.UniqueReverse.recover changed compiled.source.rawMain).isNone) s!"{name}: specialization accepted"
    names := names ++ [name]
  need ((IxIR0.UniqueReverse.recover ((recovery.address, .defn .shared .erased) :: entries)
    compiled.source.rawMain).isNone) "specialization address collision accepted"
  names := names ++ ["instance-address-conflict"]
  for (name, entry) in [("entry-shared-result", { source.entry with source := .ref 0 #[] }),
      ("entry-free-variable", { source.entry with source := .var 0 }),
      ("entry-unresolved-share", { source.entry with source := .share 0 })] do
    need (rejected (compile source.constants entry source.config)) s!"{name}: source compiler accepted"
    names := names ++ [name]
  let entryBound := { source.config with limits := { source.config.limits with
    maxExpressionUnits := (Work.programStats source.constants).expressionUnits } }
  match compile source.constants source.entry entryBound with
  | .error (.source (.resource exceeded)) =>
      need (exceeded.metric == .programExpressionUnits) "wrong closed-entry work limit"
  | _ => throw "closed entry escaped structural preflight"
  names := names ++ ["closed-entry-work-budget"]
  let baseline := IxIR2.UniqueLower.program plan false
  let optimized := target.selection.program
  let fn := IxIR2.UniqueLower.function schema true
  let cons := IxIR2.UniqueLower.consBlock schema true
  let nil := IxIR2.UniqueLower.nilBlock schema
  let context := IxIR2.UniqueLower.context schema
  for (name, changed) in [
      ("target-duplicate-credit", { cons with instructions := cons.instructions.push (.discardCredit 0) }),
      ("target-stranded-credit", { cons with
        instructions := #[.takeUnique (.reg 1) (consId schema)]
        terminator := .tailCallSelf #[.reg 0, .reg 3] }),
      ("target-use-after-take", { cons with instructions := #[.takeUnique (.reg 1) (consId schema),
        .allocWith 0 .unique (consId schema) #[.reg 2, .reg 1]] }),
      ("target-duplicate-unique-field", { cons with instructions := #[.takeUnique (.reg 1) (consId schema),
        .allocWith 0 .unique (consId schema) #[.reg 0, .reg 0]] }),
      ("target-shared-reset-of-unique", { cons with instructions := #[.resetShared (.reg 1) (consId schema),
        .allocWith 0 .unique (consId schema) #[.reg 2, .reg 0]] }),
      ("target-wrong-constructor", { cons with instructions := #[.takeUnique (.reg 1) (nilId schema),
        .allocWith 0 .unique (consId schema) #[.reg 2, .reg 0]] })] do
    let program := { optimized with declarations := [(functionAddress schema, .fn { fn with blocks := fn.blocks.set! 2 changed })] }
    need (rejected (IxIR2.Validate.validate context program)) s!"{name}: validator accepted"
    names := names ++ [name]
  let leaked := { optimized with declarations := [(functionAddress schema,
    .fn { fn with blocks := fn.blocks.set! 1 { nil with instructions := #[] } })] }
  need (rejected (IxIR2.Validate.validate context leaked)) "nil owner leaked through target return"
  names := names ++ ["target-nil-leak"]
  let foreign := { consId schema with cidx := 2 }
  let foreignSchemas := fun world cid => if world == .unique && cid == foreign then
    some { layout := Address.replicate 13, fields := #[.unique, .unique] : IxIR2.CtorSchema }
    else context.schemas world cid
  let foreignContext : IxIR2.Validate.Context := { schemas := foreignSchemas }
  let foreignCons := { cons with
    instructions := #[.takeUnique (.reg 1) (consId schema), .allocWith 0 .unique foreign #[.reg 2, .reg 0]] }
  let mismatch := { optimized with declarations := [(functionAddress schema, .fn { fn with blocks := fn.blocks.set! 2 foreignCons })] }
  need (rejected (IxIR2.Validate.validate foreignContext mismatch)) "incompatible credit layout accepted"
  names := names ++ ["target-layout-mismatch"]
  let liveSite := { IxIR2.UniqueLower.consBlock schema false with
    terminator := .tailCallSelf #[.reg 1, .reg 3] }
  need (((IxIR2.Reuse.inferPlacementWith IxIR2.Validate.defaultLimits liveSite 1 0).toOption.bind id).isNone)
    "liveness accepted an owner used after take"
  names := names ++ ["later-owner-use"]
  for (name, policy) in [("disabled-baseline", { enabled := false : IxIR2.UniqueLower.ReusePolicy }),
      ("budget-baseline", { maxRewrites := 0 : IxIR2.UniqueLower.ReusePolicy })] do
    let selected := IxIR2.UniqueLower.select plan IxIR2.Validate.defaultLimits target.translation.checked policy
    need (!selected.reused && toJson selected.program == toJson baseline) s!"{name}: changed checked fallback"
    names := names ++ [name]
  let skipped ← (compile source.constants source.entry source.config 1000 1000 1000
    { IxIR2.Validate.defaultLimits with maxBlocks := 0 }).mapError reprStr
  match skipped.backend with
  | .ownedOnly _ =>
      need ((mainCode skipped.plan).bytes == (mainCode plan).bytes &&
        Coverage.ir1Entries (declarations skipped.plan.schema) == Coverage.ir1Entries (declarations schema))
        "target failure changed consuming fallback"
      discard <| observe1 source skipped.plan
  | _ => throw "target limit did not retain the consuming fallback"
  names := names ++ ["target-budget-owned-fallback"]
  let evalContext := IxIR2.Eval.Context.ofProgram optimized context.schemas
  need (match IxIR2.Eval.runMain evalContext .physical optimized 21 0 with
    | .error .controlFuel => true | _ => false) "insufficient control budget was ignored"
  let result ← (IxIR2.Eval.runMain evalContext .physical optimized 22 0).mapError reprStr
  need (match IxIR2.Eval.dropUnique 6 result.store result.value with
    | .error .heapFuel => true | _ => false) "insufficient reclamation budget was ignored"
  names := names ++ ["control-budget-independent", "reclamation-budget-independent"]
  return names

def runAll : Except String (List CaseResult × List String) := do
  let results ← cases.mapM fun (name, values, policy) =>
    (runCase name values policy).mapError (fun error => s!"{name}: {error}")
  return (results, ← rejectionChecks)

def report (results : List CaseResult) (checks : List String) : Json :=
  Json.mkObj [("format", toJson "compilatrix/source-unique-reuse-report/1"),
    ("cases", toJson (results.map (·.summary))), ("policy_and_rejection_checks", toJson checks)]

end Ix.Compiler.UniqueReuse.Examples
