import Ix.Compiler.IxIR2.CreditPolicy
import Std.Data.HashMap

/-!
# Bounded executable validation for IxIR₂

The checker treats the CFG and its capability annotations as untrusted input.
It reconstructs ownership flow within every block, checks complete transfer at
every edge, validates borrow/lender remapping, and keeps reuse credits linear
in a register file separate from ordinary values.

All traversals are structurally finite, and explicit limits reject oversized
artifacts before they can make certificate checking unexpectedly expensive.
-/

namespace Ix.Compiler.IxIR2.Validate

open Ix.Compiler.Ixon (Address Owned)
open Ix.Compiler.IxIR2

/-- Stable identity for the function currently being checked. -/
inductive Owner where
  | main
  | declaration (address : Address)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure Site where
  owner : Owner
  block : BlockId
  instruction : Option Nat := none
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- A checked fact permitting the deliberately narrow v0 shallow-free rule. -/
structure ScalarLeafFact where
  owner : Owner
  block : BlockId
  value : ValueId
  cid : CtorId
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Trusted inputs selected by the enclosing certificate boundary.  Constructor
schemas are keyed by world because unique and shared layouts may differ. -/
structure Context where
  schemas : Owned → CtorId → Option CtorSchema := fun _ _ => none
  scalarLeaves : List ScalarLeafFact := []
  /-- Generic tooling may opt in; validator-gated compilation leaves this off. -/
  allowExtern : Bool := false

/-- Explicit denial-of-service bounds for untrusted CFGs and sidecars. -/
structure Limits where
  maxDeclarations : Nat := 4096
  maxBlocks : Nat := 16384
  maxBlocksPerFunction : Nat := 4096
  maxInstructionsPerBlock : Nat := 65536
  maxValueParams : Nat := 4096
  maxCreditParams : Nat := 4096
  maxOperands : Nat := 4096
  maxAlternatives : Nat := 4096
  maxValueRegisters : Nat := 262144
  maxCreditRegisters : Nat := 262144
  maxScalarLeafFacts : Nat := 65536
  maxFlowWork : Nat := 16777216
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def defaultLimits : Limits := {}

inductive Resource where
  | declarations
  | blocks
  | blocksPerFunction
  | instructionsPerBlock
  | valueParameters
  | creditParameters
  | operands
  | alternatives
  | valueRegisters
  | creditRegisters
  | scalarLeafFacts
  | flowWork
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Coarse, stable rejection classes.  Human-readable detail remains free to
improve without making callers parse strings. -/
inductive Violation where
  | signature
  | schema
  | register
  | ownership
  | borrow
  | credit
  | call
  | controlFlow
  | resources
  | externBoundary
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

inductive Error where
  | limit (site : Site) (resource : Resource) (actual maximum : Nat)
  | duplicateDeclaration (address : Address)
  | invalid (site : Site) (violation : Violation) (detail : String)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Structural work accepted by a successful validation. -/
structure Stats where
  declarations : Nat := 0
  functions : Nat := 0
  blocks : Nat := 0
  instructions : Nat := 0
  edges : Nat := 0
  flowWork : Nat := 0
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def Stats.add (left right : Stats) : Stats :=
  { declarations := left.declarations + right.declarations
    functions := left.functions + right.functions
    blocks := left.blocks + right.blocks
    instructions := left.instructions + right.instructions
    edges := left.edges + right.edges
    flowWork := left.flowWork + right.flowWork }

private abbrev Check := Except Error

private def failAt (site : Site) (violation : Violation) (detail : String) :
    Check α :=
  .error (.invalid site violation detail)

private def checkLimit (site : Site) (resource : Resource)
    (actual maximum : Nat) : Check Unit :=
  if actual ≤ maximum then
    return ()
  else
    .error (.limit site resource actual maximum)

private def instructionSite (site : Site) (index : Nat) : Site :=
  { site with instruction := some index }

private def foldIdxM (xs : List α) (initial : σ)
    (step : Nat → σ → α → Check σ) : Check σ :=
  let rec go (index : Nat) (state : σ) : List α → Check σ
    | [] => return state
    | value :: rest => do
        let state ← step index state value
        go (index + 1) state rest
  go 0 initial xs

/-! ## Sparse last-use indexing for non-lexical borrow death -/

private abbrev LastUses := Std.HashMap ValueId Nat

private def recordAtomUse (position : Nat) (uses : LastUses) : Atom → LastUses
  | .reg id => uses.insert id position
  | .lit _ | .erased => uses

private def recordAtomUses (position : Nat) (uses : LastUses)
    (atoms : Array Atom) : LastUses :=
  atoms.foldl (recordAtomUse position) uses

private def recordEdgeUses (position : Nat) (uses : LastUses)
    (edge : Edge) : LastUses :=
  recordAtomUses position uses edge.values

private def recordInstrUses (position : Nat) (uses : LastUses) :
    Instr → LastUses
  | .move value => recordAtomUse position uses value
  | .alloc _ _ args | .allocWith _ _ _ args =>
      recordAtomUses position uses args
  | .discardCredit _ => uses
  | .takeUnique target _ | .resetShared target _ |
      .retainShared target | .releaseShared target | .dropUnique target |
      .freeUnique target _ | .fetch target _ _ =>
      recordAtomUse position uses target
  | .call _ args | .callSelf args | .papp _ args | .extern _ args =>
      recordAtomUses position uses args
  | .apply function args =>
      recordAtomUses position (recordAtomUse position uses function) args

private def recordTerminatorUses (position : Nat) (uses : LastUses) :
    Terminator → LastUses
  | .jump edge => recordEdgeUses position uses edge
  | .switchValue scrutinee constructors natPeel =>
      let uses := recordAtomUse position uses scrutinee
      let uses := constructors.foldl
        (fun current alternative => recordEdgeUses position current alternative.edge) uses
      match natPeel with
      | none => uses
      | some peel =>
          recordEdgeUses position (recordEdgeUses position uses peel.zero) peel.succ
  | .branchCredit _ someEdge noneEdge =>
      recordEdgeUses position (recordEdgeUses position uses someEdge) noneEdge
  | .ret value => recordAtomUse position uses value
  | .tailCall _ args | .tailCallSelf args => recordAtomUses position uses args

private def lastUses (block : Block) : LastUses :=
  let rec go (position : Nat) (uses : LastUses) : List Instr → LastUses
    | [] => recordTerminatorUses position uses block.terminator
    | instruction :: rest =>
        go (position + 1) (recordInstrUses position uses instruction) rest
  go 0 {} block.instructions.toList

/-! ## Capability-flow state -/

private structure Flow where
  values : Array ValueCap
  valueLive : Array Bool
  credits : Array CreditCap
  creditLive : Array Bool
  lastUses : LastUses
  loanLastUses : LastUses
  position : Nat

private def valueCapIsOwner : ValueCap → Bool
  | .owned _ => true
  | _ => false

private def recordLoanLastUse (uses : LastUses) (loans : LastUses)
    (id : ValueId) (capability : ValueCap) : LastUses :=
  match capability, uses.get? id with
  | .borrowed _ (.value lender), some finalUse =>
      let previous := (loans.get? lender).getD 0
      loans.insert lender (max previous finalUse)
  | _, _ => loans

private def Flow.ofBlock (block : Block) (uses : LastUses) : Flow :=
  let loans := (List.range block.valueParams.size).foldl (fun current id =>
    match (block.valueParams)[id]? with
    | some capability => recordLoanLastUse uses current id capability
    | none => current) {}
  { values := block.valueParams
    valueLive := block.valueParams.map valueCapIsOwner
    credits := block.creditParams
    creditLive := block.creditParams.map fun _ => true
    lastUses := uses
    loanLastUses := loans
    position := 0 }

private def Flow.pushValue (limits : Limits) (site : Site)
    (flow : Flow) (capability : ValueCap) : Check Flow := do
  let size := flow.values.size + 1
  checkLimit site .valueRegisters size limits.maxValueRegisters
  let id := flow.values.size
  return { flow with
    values := flow.values.push capability
    valueLive := flow.valueLive.push (valueCapIsOwner capability)
    loanLastUses := recordLoanLastUse flow.lastUses flow.loanLastUses id capability }

private def Flow.pushCredit (limits : Limits) (site : Site)
    (flow : Flow) (capability : CreditCap) : Check Flow := do
  let size := flow.credits.size + 1
  checkLimit site .creditRegisters size limits.maxCreditRegisters
  return { flow with
    credits := flow.credits.push capability
    creditLive := flow.creditLive.push true }

private def Flow.liveValue (flow : Flow) (id : ValueId) : Bool :=
  ((flow.valueLive)[id]?).getD false

private def Flow.liveCredit (flow : Flow) (id : CreditId) : Bool :=
  ((flow.creditLive)[id]?).getD false

private def Flow.killValue (flow : Flow) (id : ValueId) : Flow :=
  { flow with valueLive := flow.valueLive.setIfInBounds id false }

private def Flow.killCredit (flow : Flow) (id : CreditId) : Flow :=
  { flow with creditLive := flow.creditLive.setIfInBounds id false }

private def readReg (site : Site) (flow : Flow) (id : ValueId) :
    Check ValueCap := do
  let capability ← match (flow.values)[id]? with
    | none => failAt site .register s!"unknown value register {id}"
    | some capability => pure capability
  match capability with
  | .scalar => return .scalar
  | .owned world =>
      if flow.liveValue id then
        return .owned world
      else
        failAt site .ownership s!"value register {id} has already been consumed"
  | .borrowed world .caller => return .borrowed world .caller
  | .borrowed world (.value lender) =>
      match (flow.values)[lender]? with
      | some (.owned lenderWorld) =>
          if lenderWorld != world then
            failAt site .borrow
              s!"borrow {id} and lender {lender} have different worlds"
          else if flow.liveValue lender then
            return .borrowed world (.value lender)
          else
            failAt site .borrow s!"borrow {id} outlives lender {lender}"
      | _ => failAt site .borrow s!"borrow {id} has no owning lender {lender}"

private def readAtom (site : Site) (flow : Flow) : Atom → Check ValueCap
  | .reg id => readReg site flow id
  | .lit _ | .erased => return .scalar

private def ensureNoLiveLoans (site : Site) (flow : Flow) (lender : ValueId)
    (_remaining : List Instr) (_terminator : Terminator) : Check Unit :=
  if (flow.loanLastUses.get? lender).any fun finalUse => flow.position < finalUse then
    failAt site .borrow s!"owner {lender} is consumed before its last loan use"
  else
    return ()

/-- Consume an argument for an owned interface.  Scalars dynamically satisfy
either world and therefore carry no token. -/
private def consumeExpected (site : Site) (flow : Flow) (value : Atom)
    (expected : Owned) (remaining : List Instr) (terminator : Terminator) :
    Check Flow := do
  match value with
  | .lit _ | .erased => return flow
  | .reg id =>
      match ← readReg site flow id with
      | .scalar => return flow
      | .owned world =>
          if world != expected then
            failAt site .ownership s!"value {id} has the wrong ownership world"
          else
            ensureNoLiveLoans site flow id remaining terminator
            return flow.killValue id
      | .borrowed _ _ =>
          failAt site .ownership s!"borrowed value {id} cannot transfer ownership"

/-- Consume a concrete heap owner; unlike an interface argument, a scalar is
not accepted. -/
private def consumeConcrete (site : Site) (flow : Flow) (value : Atom)
    (expected : Owned) (remaining : List Instr) (terminator : Terminator) :
    Check (Flow × ValueId) := do
  match value with
  | .reg id =>
      match ← readReg site flow id with
      | .owned world =>
          if world != expected then
            failAt site .ownership s!"value {id} has the wrong ownership world"
          else
            ensureNoLiveLoans site flow id remaining terminator
            return (flow.killValue id, id)
      | .scalar => failAt site .ownership "a constructor location was required"
      | .borrowed _ _ => failAt site .ownership "a borrowed constructor cannot be consumed"
  | .lit _ | .erased => failAt site .ownership "a constructor location was required"

private def observeExpected (site : Site) (flow : Flow) (value : Atom)
    (expected : Owned) : Check Unit := do
  match ← readAtom site flow value with
  | .scalar => return ()
  | .owned world | .borrowed world _ =>
      if world == expected then
        return ()
      else
        failAt site .ownership "observed value has the wrong ownership world"

private def requireStaticScalar (site : Site) (flow : Flow)
    (value : Atom) : Check Unit := do
  match ← readAtom site flow value with
  | .scalar => return ()
  | _ => failAt site .externBoundary "extern operands must be statically scalar"

private def getCredit (site : Site) (flow : Flow) (id : CreditId) :
    Check CreditCap := do
  match (flow.credits)[id]? with
  | none => failAt site .register s!"unknown credit register {id}"
  | some capability =>
      if flow.liveCredit id then
        return capability
      else
        failAt site .credit s!"credit register {id} has already been consumed"

private def consumeCredit (site : Site) (flow : Flow) (id : CreditId)
    (layout : Option LayoutId := none) : Check Flow := do
  let capability ← getCredit site flow id
  match layout with
  | none => return flow.killCredit id
  | some expected =>
      let actual := match capability with
        | .required found | .optional found => found
      if actual == expected then
        return flow.killCredit id
      else
        failAt site .credit "reuse credit has an incompatible layout"

private def lookupSchema (limits : Limits) (context : Context) (site : Site)
    (world : Owned) (cid : CtorId) : Check CtorSchema := do
  let schema ← match context.schemas world cid with
    | none => failAt site .schema "missing constructor schema"
    | some schema => pure schema
  checkLimit site .operands schema.fields.size limits.maxOperands
  if schema.fields.all fun fieldWorld => fieldWorld == world then
    return schema
  else
    failAt site .schema "v0 constructor fields do not agree with their representation world"

private def appendFields (limits : Limits) (site : Site) (flow : Flow)
    (fields : Array Owned) : Check Flow :=
  fields.toList.foldlM
    (fun current world => current.pushValue limits site (.owned world)) flow

private abbrev DeclarationIndex := Std.HashMap Address Decl

private def declarationIndex (declarations : List (Address × Decl)) :
    DeclarationIndex :=
  declarations.foldl (fun index entry => index.insert entry.1 entry.2) {}

private def declarationAt? (index : DeclarationIndex) (address : Address) :
    Option Decl :=
  index.get? address

private def duplicateAddress? : List (Address × Decl) → Option Address :=
  let rec go (seen : Std.HashMap Address Unit) :
      List (Address × Decl) → Option Address
    | [] => none
    | (address, _) :: rest =>
        if (seen.get? address).isSome then some address
        else go (seen.insert address ()) rest
  go {}

/-! ## Instruction transfer -/

private def checkOperandCount (limits : Limits) (site : Site)
    (operands : Array α) : Check Unit :=
  checkLimit site .operands operands.size limits.maxOperands

private def edgeSyntaxWork (edge : Edge) : Nat :=
  1 + edge.values.size + edge.credits.size

private def instructionSyntaxWork : Instr → Nat
  | .alloc _ _ arguments | .allocWith _ _ _ arguments |
      .call _ arguments | .callSelf arguments | .papp _ arguments |
      .extern _ arguments => 1 + arguments.size
  | .apply _ arguments => 2 + arguments.size
  | _ => 2

private def terminatorSyntaxWork : Terminator → Nat
  | .jump edge => edgeSyntaxWork edge
  | .switchValue _ constructors natPeel =>
      2 + constructors.size * constructors.size +
        constructors.foldl (fun total alternative =>
          total + edgeSyntaxWork alternative.edge) 0 +
        match natPeel with
        | none => 0
        | some peel => edgeSyntaxWork peel.zero + edgeSyntaxWork peel.succ
  | .branchCredit _ someEdge noneEdge =>
      1 + edgeSyntaxWork someEdge + edgeSyntaxWork noneEdge
  | .ret _ => 2
  | .tailCall _ arguments | .tailCallSelf arguments => 1 + arguments.size

private def checkEdgeSyntaxBounds (limits : Limits) (site : Site)
    (edge : Edge) : Check Unit := do
  checkOperandCount limits site edge.values
  checkOperandCount limits site edge.credits

private def checkInstructionSyntaxBounds (limits : Limits) (site : Site) :
    Instr → Check Unit
  | .alloc _ _ arguments | .allocWith _ _ _ arguments |
      .call _ arguments | .callSelf arguments | .papp _ arguments |
      .extern _ arguments | .apply _ arguments =>
      checkOperandCount limits site arguments
  | _ => return ()

private def checkTerminatorSyntaxBounds (limits : Limits) (site : Site) :
    Terminator → Check Unit
  | .jump edge => checkEdgeSyntaxBounds limits site edge
  | .switchValue _ constructors natPeel => do
      let alternatives := constructors.size + if natPeel.isSome then 2 else 0
      checkLimit site .alternatives alternatives limits.maxAlternatives
      for alternative in constructors do
        checkEdgeSyntaxBounds limits site alternative.edge
      match natPeel with
      | none => return ()
      | some peel =>
          checkEdgeSyntaxBounds limits site peel.zero
          checkEdgeSyntaxBounds limits site peel.succ
  | .branchCredit _ someEdge noneEdge => do
      checkEdgeSyntaxBounds limits site someEdge
      checkEdgeSyntaxBounds limits site noneEdge
  | .ret _ => return ()
  | .tailCall _ arguments | .tailCallSelf arguments =>
      checkOperandCount limits site arguments

private def checkBlockSyntaxBounds (limits : Limits) (site : Site)
    (block : Block) : Check Nat := do
  for instruction in block.instructions do
    checkInstructionSyntaxBounds limits site instruction
  checkTerminatorSyntaxBounds limits site block.terminator
  let work := block.instructions.foldl
    (fun total instruction => total + instructionSyntaxWork instruction) 0 +
      terminatorSyntaxWork block.terminator
  checkLimit site .flowWork work limits.maxFlowWork
  return work

private def consumeFieldArguments (limits : Limits) (site : Site)
    (flow : Flow) (arguments : Array Atom) (fields : Array Owned)
    (remaining : List Instr) (terminator : Terminator) : Check Flow := do
  checkOperandCount limits site arguments
  if arguments.size != fields.size then
    failAt site .schema "constructor argument count does not match its schema"
  else
    (arguments.toList.zip fields.toList).foldlM
      (fun current pair =>
        consumeExpected site current pair.1 pair.2 remaining terminator) flow

private def checkCallArity (limits : Limits) (site : Site)
    (arguments : Array Atom) (signature : Signature) : Check Unit := do
  checkOperandCount limits site arguments
  if arguments.size == signature.params.size then
    return ()
  else
    failAt site .call "call arity does not match the addressed signature"

/-- Owned arguments are processed before borrowed arguments.  Thus passing an
owner and one of its loans to the same call is rejected regardless of their
parameter order. -/
private def checkCallArguments (limits : Limits) (site : Site) (flow : Flow)
    (arguments : Array Atom) (signature : Signature)
    (remaining : List Instr) (terminator : Terminator) : Check Flow := do
  checkCallArity limits site arguments signature
  let pairs := arguments.toList.zip signature.params.toList
  let flow ← pairs.foldlM (fun current pair =>
    match pair.2.passing with
    | .owned =>
        consumeExpected site current pair.1 pair.2.world remaining terminator
    | .borrowed => return current) flow
  pairs.foldlM (fun current pair => do
    match pair.2.passing with
    | .owned => return current
    | .borrowed =>
        observeExpected site current pair.1 pair.2.world
        return current) flow

private def checkPapSignature (site : Site) (signature : Signature) :
    Check Unit :=
  if signature.papSafe && signature.result == .shared &&
      signature.params.all fun parameter =>
        parameter.passing == .owned && parameter.world == .shared then
    return ()
  else
    failAt site .call "partial application target is not papSafe"

private def consumePapArguments (limits : Limits) (site : Site) (flow : Flow)
    (arguments : Array Atom) (signature : Signature)
    (remaining : List Instr) (terminator : Terminator) : Check Flow := do
  checkOperandCount limits site arguments
  checkPapSignature site signature
  if arguments.size < signature.params.size then
    arguments.toList.foldlM
      (fun current argument =>
        consumeExpected site current argument .shared remaining terminator) flow
  else
    failAt site .call "partial application must be strictly under-saturated"

private def consumeApplyArguments (limits : Limits) (site : Site) (flow : Flow)
    (function : Atom) (arguments : Array Atom) (remaining : List Instr)
    (terminator : Terminator) : Check Flow := do
  checkOperandCount limits site arguments
  let flow ← consumeExpected site flow function .shared remaining terminator
  arguments.toList.foldlM
    (fun current argument =>
      consumeExpected site current argument .shared remaining terminator) flow

private def ensureNoLiveCallCredit (site : Site) (flow : Flow) : Check Unit :=
  if flow.creditLive.any id then
    failAt site .credit "reuse credits cannot remain live across a call boundary"
  else
    return ()

private def appendCallResult (limits : Limits) (site : Site) (flow : Flow)
    (signature : Signature) : Check Flow :=
  flow.pushValue limits site (.owned signature.result)

private def validateInstruction (policy : CreditPolicy)
    (limits : Limits) (context : Context)
    (declarations : DeclarationIndex) (signature : Signature) (site : Site)
    (flow : Flow) (instruction : Instr) (remaining : List Instr)
    (terminator : Terminator) : Check Flow := do
  match instruction with
  | .move value =>
      match value with
      | .lit _ | .erased => flow.pushValue limits site .scalar
      | .reg id =>
          match ← readReg site flow id with
          | .scalar => flow.pushValue limits site .scalar
          | .borrowed world lender =>
              flow.pushValue limits site (.borrowed world lender)
          | .owned world =>
              ensureNoLiveLoans site flow id remaining terminator
              (flow.killValue id).pushValue limits site (.owned world)
  | .alloc world cid arguments =>
      let schema ← lookupSchema limits context site world cid
      let flow ← consumeFieldArguments limits site flow arguments schema.fields
        remaining terminator
      flow.pushValue limits site (.owned world)
  | .allocWith credit world cid arguments =>
      let schema ← lookupSchema limits context site world cid
      let flow ← consumeCredit site flow credit (some schema.layout)
      let flow ← consumeFieldArguments limits site flow arguments schema.fields
        remaining terminator
      flow.pushValue limits site (.owned world)
  | .discardCredit credit => consumeCredit site flow credit
  | .takeUnique target cid =>
      let schema ← lookupSchema limits context site .unique cid
      let (flow, _) ← consumeConcrete site flow target .unique remaining terminator
      let flow ← appendFields limits site flow schema.fields
      flow.pushCredit limits site (.required schema.layout)
  | .resetShared target cid =>
      let schema ← lookupSchema limits context site .shared cid
      let (flow, _) ← consumeConcrete site flow target .shared remaining terminator
      let flow ← appendFields limits site flow schema.fields
      flow.pushCredit limits site (.optional schema.layout)
  | .retainShared target =>
      match ← readAtom site flow target with
      | .scalar => flow.pushValue limits site .scalar
      | .owned .shared | .borrowed .shared _ =>
          flow.pushValue limits site (.owned .shared)
      | .owned .unique | .borrowed .unique _ =>
          failAt site .ownership "retainShared requires a shared value"
  | .releaseShared target =>
      consumeExpected site flow target .shared remaining terminator
  | .dropUnique target =>
      consumeExpected site flow target .unique remaining terminator
  | .freeUnique target cid =>
      let _ ← lookupSchema limits context site .unique cid
      let (flow, id) ← consumeConcrete site flow target .unique remaining terminator
      if context.scalarLeaves.any fun fact =>
          fact.owner == site.owner && fact.block == site.block &&
            fact.value == id && fact.cid == cid then
        return flow
      else
        failAt site .schema "freeUnique requires an exact checked scalar-leaf fact"
  | .fetch target cid field =>
      let capability ← readAtom site flow target
      let (world, lender) ← match capability, target with
        | .owned world, .reg id => pure (world, BorrowLender.value id)
        | .borrowed world lender, _ => pure (world, lender)
        | .scalar, _ => failAt site .ownership "fetch requires a constructor location"
        | .owned _, _ => failAt site .register "an owned fetch target must be a register"
      let schema ← lookupSchema limits context site world cid
      match (schema.fields)[field]? with
      | none => failAt site .schema s!"constructor field {field} is out of bounds"
      | some fieldWorld =>
          flow.pushValue limits site (.borrowed fieldWorld lender)
  | .call function arguments =>
      if policy == .callLocalV0 then ensureNoLiveCallCredit site flow
      match declarationAt? declarations function with
      | some (.fn definition) =>
          let flow ← checkCallArguments limits site flow arguments
            definition.signature remaining terminator
          appendCallResult limits site flow definition.signature
      | some (.extern _) =>
          failAt site .call "extern declarations must use the extern instruction"
      | none => failAt site .call "call target is not declared"
  | .callSelf arguments =>
      if policy == .callLocalV0 then ensureNoLiveCallCredit site flow
      let flow ← checkCallArguments limits site flow arguments
        signature remaining terminator
      appendCallResult limits site flow signature
  | .papp function arguments =>
      ensureNoLiveCallCredit site flow
      match declarationAt? declarations function with
      | some (.fn definition) =>
          let flow ← consumePapArguments limits site flow arguments
            definition.signature remaining terminator
          flow.pushValue limits site (.owned .shared)
      | some (.extern arity) =>
          if !context.allowExtern then
            failAt site .externBoundary "extern partial applications are forbidden"
          else if arguments.size >= arity then
            failAt site .call "extern partial application must be under-saturated"
          else
            checkOperandCount limits site arguments
            for argument in arguments do
              requireStaticScalar site flow argument
            flow.pushValue limits site (.owned .shared)
      | none => failAt site .call "partial-application target is not declared"
  | .apply function arguments =>
      ensureNoLiveCallCredit site flow
      let flow ← consumeApplyArguments limits site flow function arguments
        remaining terminator
      flow.pushValue limits site (.owned .shared)
  | .extern function arguments =>
      ensureNoLiveCallCredit site flow
      if !context.allowExtern then
        failAt site .externBoundary "extern instructions are forbidden"
      else
        match declarationAt? declarations function with
        | some (.extern arity) =>
            checkOperandCount limits site arguments
            if arguments.size != arity then
              failAt site .call "extern arity does not match its declaration"
            else
              for argument in arguments do
                requireStaticScalar site flow argument
              flow.pushValue limits site .scalar
        | some (.fn _) => failAt site .call "extern target is a compiler function"
        | none => failAt site .call "extern target is not declared"

/-! ## Edge transfer and terminators -/

private inductive IncomingValue where
  | implicitScalar
  | explicit (value : Atom)

private inductive SourceRoot where
  | caller
  | local (id : ValueId)
  deriving BEq

private def incomingCapability (site : Site) (flow : Flow) :
    IncomingValue → Check ValueCap
  | .implicitScalar => return .scalar
  | .explicit value => readAtom site flow value

private def incomingSourceRoot (incoming : IncomingValue)
    (capability : ValueCap) : Option SourceRoot :=
  match incoming, capability with
  | .explicit (.reg id), .owned _ => some (.local id)
  | _, .borrowed _ .caller => some .caller
  | _, .borrowed _ (.value lender) => some (.local lender)
  | _, _ => none

private def validateBorrowMapping (site : Site) (flow : Flow)
    (incoming : List IncomingValue) (parameters : Array ValueCap)
    (argument : IncomingValue) (world : Owned) (lender : BorrowLender) :
    Check Unit := do
  let capability ← incomingCapability site flow argument
  match capability with
  | .scalar => return ()
  | .owned sourceWorld | .borrowed sourceWorld _ =>
      if sourceWorld != world then
        failAt site .borrow "borrowed edge argument has the wrong world"
      else
        match lender with
        | .caller =>
            match incomingSourceRoot argument capability with
            | some .caller => return ()
            | _ => failAt site .borrow "a caller-rooted target borrow requires a caller-rooted source borrow"
        | .value targetLender =>
            match (parameters)[targetLender]?, incoming[targetLender]? with
            | some (.owned lenderWorld), some lenderArgument =>
                if lenderWorld != world then
                  failAt site .borrow "target borrow and lender parameters have different worlds"
                else
                  let lenderCapability ← incomingCapability site flow lenderArgument
                  match incomingSourceRoot lenderArgument lenderCapability,
                      incomingSourceRoot argument capability with
                  | some (.local expected), some (.local actual) =>
                      if expected == actual then return ()
                      else failAt site .borrow "edge borrow does not map to its transferred lender"
                  | _, _ => failAt site .borrow "edge borrow requires a concrete transferred local lender"
            | _, _ => failAt site .borrow "target borrow names a non-owning or missing parameter"

private def validateIncomingValue (site : Site) (flow : Flow)
    (incoming : List IncomingValue) (parameters : Array ValueCap)
    (argument : IncomingValue) (parameter : ValueCap) : Check Unit := do
  match argument, parameter with
  | .implicitScalar, .scalar => return ()
  | .implicitScalar, _ =>
      failAt site .controlFlow "the Nat successor predecessor requires a scalar parameter"
  | .explicit _, _ =>
      let capability ← incomingCapability site flow argument
      match parameter with
      | .scalar =>
          match capability with
          | .scalar => return ()
          | _ => failAt site .controlFlow "a possibly heap-bearing value cannot enter a scalar block parameter"
      | .owned world =>
          match capability with
          | .scalar => return ()
          | .owned sourceWorld =>
              if sourceWorld == world then return ()
              else failAt site .ownership "edge owner has the wrong world"
          | .borrowed _ _ => failAt site .ownership "a borrowed edge value cannot enter an owning parameter"
      | .borrowed world lender =>
          validateBorrowMapping site flow incoming parameters argument world lender

private def consumeIncomingOwner (site : Site) (flow : Flow)
    (argument : IncomingValue) (parameter : ValueCap) : Check Flow := do
  match parameter, argument with
  | .owned _, .implicitScalar => return flow
  | .owned world, .explicit value =>
      match value with
      | .lit _ | .erased => return flow
      | .reg id =>
          match ← readReg site flow id with
          | .scalar => return flow
          | .owned sourceWorld =>
              if sourceWorld == world then return flow.killValue id
              else failAt site .ownership "edge owner has the wrong world"
          | .borrowed _ _ => failAt site .ownership "a borrowed edge value cannot transfer ownership"
  | _, _ => return flow

private def consumeIncomingCredit (site : Site) (flow : Flow)
    (id : CreditId) (parameter : CreditCap) : Check Flow := do
  let source ← getCredit site flow id
  match parameter, source with
  | .required targetLayout, .required sourceLayout =>
      if targetLayout == sourceLayout then return flow.killCredit id
      else failAt site .credit "required edge credit has the wrong layout"
  | .required _, .optional _ =>
      failAt site .credit "an optional credit cannot narrow to required"
  | .optional targetLayout, .required sourceLayout
  | .optional targetLayout, .optional sourceLayout =>
      if targetLayout == sourceLayout then return flow.killCredit id
      else failAt site .credit "optional edge credit has the wrong layout"

private def ensureExhausted (site : Site) (flow : Flow) : Check Unit :=
  if flow.valueLive.any id then
    failAt site .resources "control transfer leaves an owned value behind"
  else if flow.creditLive.any id then
    failAt site .resources "control transfer leaves a reuse credit behind"
  else
    return ()

private def validateEdge (limits : Limits) (site : Site) (blocks : Array Block)
    (flow : Flow) (edge : Edge) (implicit : List IncomingValue := []) :
    Check Unit := do
  checkOperandCount limits site edge.values
  checkOperandCount limits site edge.credits
  let target ← match (blocks)[edge.target]? with
    | none => failAt site .controlFlow s!"edge targets missing block {edge.target}"
    | some block => pure block
  let incoming := implicit ++ edge.values.toList.map IncomingValue.explicit
  if incoming.length != target.valueParams.size then
    failAt site .controlFlow "edge value arity does not match target parameters"
  else if edge.credits.size != target.creditParams.size then
    failAt site .controlFlow "edge credit arity does not match target parameters"
  else
    let valuePairs := incoming.zip target.valueParams.toList
    for pair in valuePairs do
      validateIncomingValue site flow incoming target.valueParams pair.1 pair.2
    let flow ← valuePairs.foldlM
      (fun current pair => consumeIncomingOwner site current pair.1 pair.2) flow
    let creditPairs := edge.credits.toList.zip target.creditParams.toList
    let flow ← creditPairs.foldlM
      (fun current pair => consumeIncomingCredit site current pair.1 pair.2) flow
    ensureExhausted site flow

private def duplicateCtor? : List CtorId → Option CtorId :=
  let rec go (seen : List CtorId) : List CtorId → Option CtorId
    | [] => none
    | cid :: rest =>
        if seen.any (· == cid) then some cid else go (cid :: seen) rest
  go []

private def checkTailArguments (limits : Limits) (site : Site) (flow : Flow)
    (arguments : Array Atom) (signature : Signature)
    (remaining : List Instr) (terminator : Terminator) : Check Flow := do
  checkCallArity limits site arguments signature
  let pairs := arguments.toList.zip signature.params.toList
  let flow ← pairs.foldlM (fun current pair =>
    match pair.2.passing with
    | .owned =>
        consumeExpected site current pair.1 pair.2.world remaining terminator
    | .borrowed => return current) flow
  pairs.foldlM (fun current pair => do
    match pair.2.passing with
    | .owned => return current
    | .borrowed =>
        match ← readAtom site current pair.1 with
        | .scalar => return current
        | .borrowed world .caller =>
            if world == pair.2.world then return current
            else failAt site .borrow "tail borrow has the wrong world"
        | .borrowed _ (.value _) => failAt site .borrow "a borrow rooted in a local owner cannot escape through a tail call"
        | .owned _ => failAt site .borrow "an owned local value cannot enter a borrowed tail parameter") flow

private def validateTerminator (limits : Limits) (context : Context)
    (declarations : DeclarationIndex) (signature : Signature) (site : Site)
    (blocks : Array Block) (flow : Flow) (terminator : Terminator) :
    Check Nat := do
  match terminator with
  | .jump edge =>
      validateEdge limits site blocks flow edge
      return 1
  | .switchValue scrutinee constructors natPeel =>
      let alternatives := constructors.size + if natPeel.isSome then 2 else 0
      checkLimit site .alternatives alternatives limits.maxAlternatives
      if alternatives == 0 then
        failAt site .controlFlow "switchValue requires at least one alternative"
      else
        match duplicateCtor? (constructors.toList.map (·.cid)) with
        | some _ => failAt site .controlFlow "switchValue repeats a constructor identity"
        | none =>
            let capability ← readAtom site flow scrutinee
            match capability with
            | .owned world | .borrowed world _ =>
                for alternative in constructors do
                  let _ ← lookupSchema limits context site world alternative.cid
                  pure ()
            | .scalar => pure ()
            for alternative in constructors do
              validateEdge limits site blocks flow alternative.edge
            match natPeel with
            | none => pure ()
            | some peel =>
                validateEdge limits site blocks flow peel.zero
                validateEdge limits site blocks flow peel.succ [.implicitScalar]
            return alternatives
  | .branchCredit credit someEdge noneEdge =>
      match ← getCredit site flow credit with
      | .required _ => failAt site .credit "branchCredit requires an optional credit"
      | .optional layout =>
          let someFlow :=
            { flow with credits := flow.credits.setIfInBounds credit (.required layout) }
          validateEdge limits site blocks someFlow someEdge
          validateEdge limits site blocks flow noneEdge
          return 2
  | .ret value =>
      let flow ← consumeExpected site flow value signature.result [] terminator
      ensureExhausted site flow
      return 0
  | .tailCall function arguments =>
      ensureNoLiveCallCredit site flow
      match declarationAt? declarations function with
      | some (.fn definition) =>
          if definition.signature.result != signature.result then
            failAt site .call "tail-call result world does not match the caller"
          else
            let flow ← checkTailArguments limits site flow arguments
              definition.signature [] terminator
            ensureExhausted site flow
            return 0
      | some (.extern _) => failAt site .call "tailCall cannot target an extern"
      | none => failAt site .call "tail-call target is not declared"
  | .tailCallSelf arguments =>
      ensureNoLiveCallCredit site flow
      let flow ← checkTailArguments limits site flow arguments signature [] terminator
      ensureExhausted site flow
      return 0

/-! ## Blocks, functions, and whole programs -/

private def expectedEntryParams (signature : Signature) : Array ValueCap :=
  signature.params.map fun parameter =>
    match parameter.passing with
    | .owned => .owned parameter.world
    | .borrowed => .borrowed parameter.world .caller

private def validateBlockParams (limits : Limits) (site : Site)
    (block : Block) : Check Unit := do
  checkLimit site .valueParameters block.valueParams.size limits.maxValueParams
  checkLimit site .creditParameters block.creditParams.size limits.maxCreditParams
  for parameter in block.valueParams do
    match parameter with
    | .borrowed world (.value lender) =>
        match (block.valueParams)[lender]? with
        | some (.owned lenderWorld) =>
            if lenderWorld == world then pure ()
            else failAt site .borrow "block borrow and lender have different worlds"
        | _ => failAt site .borrow "block borrow names a non-owning parameter"
    | _ => pure ()

private def validateBlock (policy : CreditPolicy)
    (limits : Limits) (context : Context)
    (declarations : DeclarationIndex) (signature : Signature) (owner : Owner)
    (blocks : Array Block) (blockId : BlockId) (block : Block) : Check Stats := do
  let site : Site := { owner, block := blockId }
  validateBlockParams limits site block
  checkLimit site .instructionsPerBlock block.instructions.size
    limits.maxInstructionsPerBlock
  checkLimit site .valueRegisters block.valueParams.size limits.maxValueRegisters
  checkLimit site .creditRegisters block.creditParams.size limits.maxCreditRegisters
  let syntaxWork ← checkBlockSyntaxBounds limits site block
  let uses := lastUses block
  let rec instructions (index : Nat) (flow : Flow) : List Instr → Check Flow
    | [] => return flow
    | instruction :: remaining => do
        let flow := { flow with position := index }
        let flow ← validateInstruction policy limits context declarations signature
          (instructionSite site index) flow instruction remaining block.terminator
        instructions (index + 1) flow remaining
  let flow ← instructions 0 (Flow.ofBlock block uses) block.instructions.toList
  let flow := { flow with position := block.instructions.size }
  let flowWork := syntaxWork + flow.values.size + flow.credits.size
  checkLimit site .flowWork flowWork limits.maxFlowWork
  let edges ← validateTerminator limits context declarations signature site blocks flow
    block.terminator
  let stats : Stats :=
    { blocks := 1
      instructions := block.instructions.size
      edges := edges
      flowWork := flowWork }
  return stats

private def validateSignature (limits : Limits) (site : Site)
    (signature : Signature) : Check Unit := do
  checkLimit site .valueParameters signature.params.size limits.maxValueParams
  if signature.papSafe then
    checkPapSignature site signature
  else
    return ()

private def validateFunction (policy : CreditPolicy)
    (limits : Limits) (context : Context)
    (declarations : DeclarationIndex) (owner : Owner)
    (definition : Function) : Check Stats := do
  let entrySite : Site := { owner, block := 0 }
  validateSignature limits entrySite definition.signature
  if definition.blocks.isEmpty then
    failAt entrySite .controlFlow "function has no entry block"
  else
    checkLimit entrySite .blocksPerFunction definition.blocks.size
      limits.maxBlocksPerFunction
    let entry := definition.blocks[0]!
    if entry.valueParams != expectedEntryParams definition.signature then
      failAt entrySite .signature "entry value parameters do not match the function signature"
    else if !entry.creditParams.isEmpty then
      failAt entrySite .signature "function entry cannot accept reuse credits"
    else
      let stats ← foldIdxM definition.blocks.toList ({} : Stats) fun blockId current block => do
        let blockStats ← validateBlock policy limits context declarations definition.signature owner
          definition.blocks blockId block
        let current := Stats.add current blockStats
        checkLimit entrySite .flowWork current.flowWork limits.maxFlowWork
        return current
      return { stats with functions := stats.functions + 1 }

private def structuralBlockCount (program : Program) : Nat :=
  program.main.blocks.size + program.declarations.foldl (fun total entry =>
    match entry.2 with
    | .fn definition => total + definition.blocks.size
    | .extern _ => total) 0

/-- Validate under an explicit, versioned credit boundary. Suspended credits
remain in the caller's flow, so its continuation must consume or discard them
and every outgoing edge must transfer them linearly. Function entries accept
no credits under either policy. -/
def validateWithPolicy (policy : CreditPolicy)
    (limits : Limits) (context : Context) (program : Program) :
    Except Error Stats := do
  let programSite : Site := { owner := .main, block := 0 }
  checkLimit programSite .declarations program.declarations.length
    limits.maxDeclarations
  checkLimit programSite .scalarLeafFacts context.scalarLeaves.length
    limits.maxScalarLeafFacts
  checkLimit programSite .blocks (structuralBlockCount program) limits.maxBlocks
  let declarationWork := program.declarations.length * 2
  checkLimit programSite .flowWork declarationWork limits.maxFlowWork
  if !program.main.signature.params.isEmpty then
    failAt programSite .signature "the distinguished main function must be nullary"
  else match duplicateAddress? program.declarations with
  | some address => .error (.duplicateDeclaration address)
  | none =>
      let declarations := declarationIndex program.declarations
      let declarationStats ← program.declarations.foldlM (fun current entry => do
        let next ← match entry.2 with
          | .fn definition =>
              validateFunction policy limits context declarations (.declaration entry.1) definition
          | .extern arity =>
              if !context.allowExtern then
                failAt { owner := .declaration entry.1, block := 0 }
                  .externBoundary "extern declarations are forbidden"
              else
                checkLimit programSite .operands arity limits.maxOperands
                return {}
        let current := Stats.add current next
        checkLimit programSite .flowWork current.flowWork limits.maxFlowWork
        return current) ({} : Stats)
      let mainStats ← validateFunction policy limits context declarations .main program.main
      let overhead : Stats :=
        { declarations := program.declarations.length
          flowWork := declarationWork }
      let stats := Stats.add (Stats.add declarationStats mainStats) overhead
      checkLimit programSite .flowWork stats.flowWork limits.maxFlowWork
      return stats

/-- The existing checker retains the original call-local contract. -/
def validateWith (limits : Limits) (context : Context) (program : Program) :
    Except Error Stats :=
  validateWithPolicy .callLocalV0 limits context program

def validate (context : Context) (program : Program) : Except Error Stats :=
  validateWith defaultLimits context program

/-- Proof-facing acceptance predicate for an explicitly bounded check. -/
def ValidWith (limits : Limits) (context : Context) (program : Program) : Prop :=
  ∃ stats, validateWith limits context program = .ok stats

def Valid (context : Context) (program : Program) : Prop :=
  ValidWith defaultLimits context program

/-- A checker result packaged with the equation consumed by later proofs. -/
structure Checked (limits : Limits) (context : Context) (program : Program) where
  stats : Stats
  accepted : validateWith limits context program = .ok stats

/-- Versioned acceptance retains the exact policy as part of its type. -/
structure CheckedWithPolicy (policy : CreditPolicy) (limits : Limits)
    (context : Context) (program : Program) where
  stats : Stats
  accepted : validateWithPolicy policy limits context program = .ok stats

def Checked.withPolicy {limits : Limits} {context : Context} {program : Program}
    (checked : Checked limits context program) :
    CheckedWithPolicy .callLocalV0 limits context program :=
  ⟨checked.stats, checked.accepted⟩

end Ix.Compiler.IxIR2.Validate
