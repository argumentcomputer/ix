import Compilatrix.IxIR2.Validate

/-!
# Structured IxIR₁ to IxIR₂ lowering

IxIR₁ deliberately erases two facts that IxIR₂ must check: function-parameter
worlds and the full constructor identity at `fetch`, `free`, and case sites.
The lowering context supplies exactly those owner-sensitive facts.  Everything
else here is producer-computed: blocks, SSA ordinals, capability transfer,
edge parameters, scalar-leaf facts, and the proof-facing validation equation.

The baseline is intentionally conservative.  Function parameters use the
owned IxIR₁ calling convention, raw `reuse` is rejected, and every live source
environment slot is transferred at a join.  Parameter reduction, borrowing,
and reset/reuse insertion are later checked transformations over this output.
-/

namespace Compilatrix.IxIR2.Lower

open Compilatrix.Ixon (Address Owned)
open Compilatrix.IxIR2

/-- A stable source-code coordinate. `branches` records alternative indices
from outermost to innermost; `offset` counts `letOp`s in the current arm. -/
structure SourceSite where
  owner : Validate.Owner
  branches : List Nat := []
  offset : Nat := 0
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def SourceSite.next (site : SourceSite) : SourceSite :=
  { site with offset := site.offset + 1 }

def SourceSite.alternative (site : SourceSite) (index : Nat) : SourceSite :=
  { site with branches := site.branches ++ [index], offset := 0 }

/-- Facts retained from validated IxIR₀/IxIR₁ production. Missing facts
fail closed at the operation that needs them. -/
structure Context where
  /-- Parameter worlds in call order for each addressed IxIR₁ function. -/
  parameterWorlds : Address → Option (Array Owned) := fun _ => none
  schemas : Owned → CtorId → Option CtorSchema := fun _ _ => none
  /-- Exact constructor at one IxIR₁ projection. -/
  fetchCtor : SourceSite → Option CtorId := fun _ => none
  /-- Checked all-scalar constructor at one IxIR₁ shallow free. -/
  scalarFreeCtor : SourceSite → Option CtorId := fun _ => none
  /-- Full constructor identity for an IxIR₁ alternative, when that
  alternative participates in heap-constructor dispatch. `none` permits a
  Nat-only alternative. -/
  caseCtor : SourceSite → Nat → Option CtorId := fun _ _ => none
  /-- Generic tooling may preserve scalar externs. The certified pipeline
  leaves this false. -/
  allowExtern : Bool := false
  /-- Structural recursion budget for one source-code path. -/
  maxDepth : Nat := 100000

structure Input where
  declarations : List (Address × IxIR1.Decl)
  main : IxIR1.Code
  mainResult : Owned

inductive Error where
  | duplicateDeclaration (address : Address)
  | missingParameterWorlds (address : Address)
  | signature (owner : Validate.Owner) (detail : String)
  | source (site : SourceSite) (detail : String)
  | ownership (site : SourceSite) (detail : String)
  | schema (site : SourceSite) (detail : String)
  | unsupported (site : SourceSite) (detail : String)
  | resources (site : SourceSite)
  | internal (detail : String)
  | validation (error : Validate.Error)
  deriving BEq, Repr

inductive TargetPosition where
  | instruction (index : Nat)
  | terminator
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- One source position's producer-computed target coordinate. A source arm
may occur more than once when the same IxIR₁ alternative serves both a
constructor and a literal-Nat path. -/
structure PositionTrace where
  source : SourceSite
  block : BlockId
  target : TargetPosition
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Exact environment-to-parameter transfer generated at one edge. -/
structure EdgeTrace where
  source : SourceSite
  sourceBlock : BlockId
  target : BlockId
  explicitValues : Array Atom
  targetParams : Array ValueCap
  implicitScalars : Nat := 0
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure Trace where
  positions : List PositionTrace := []
  edges : List EdgeTrace := []
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure Artifact where
  program : Program
  validationContext : Validate.Context
  trace : Trace

/-- A successful lower-and-check result retains the exact validator equation,
so later simulation files never need to trust a Boolean acceptance claim. -/
structure Checked where
  artifact : Artifact
  stats : Validate.Stats
  accepted : Validate.validate artifact.validationContext artifact.program =
    .ok stats

namespace Checked

/-- Every returned checked artifact satisfies the public bounded-validity
predicate by construction. -/
theorem valid (checked : Checked) :
    Validate.Valid checked.artifact.validationContext checked.artifact.program :=
  ⟨checked.stats, checked.accepted⟩

end Checked

private def sourceDeclAt?
    (declarations : List (Address × IxIR1.Decl)) (address : Address) :
    Option IxIR1.Decl :=
  (declarations.find? fun entry => entry.1 == address).map (fun entry => entry.2)

private def duplicateAddress? :
    List (Address × IxIR1.Decl) → Option Address
  | [] => none
  | (address, _) :: rest =>
      if rest.any fun entry => entry.1 == address then some address
      else duplicateAddress? rest

private def signatureOf (context : Context) (owner : Validate.Owner)
    (address : Address) (definition : IxIR1.FnDef) : Except Error Signature := do
  let worlds ← match context.parameterWorlds address with
    | some worlds => pure worlds
    | none => .error (.missingParameterWorlds address)
  if worlds.size != definition.arity then
    .error (.signature owner "parameter-world arity does not match IxIR₁")
  else
    let parameters := worlds.map fun world =>
      ({ world, passing := .owned } : Param)
    let signature : Signature :=
      { params := parameters
        result := definition.result
        papSafe := definition.papSafe }
    if signature.papSafe &&
        !(signature.result == .shared &&
          signature.params.all fun parameter => parameter.world == .shared) then
      .error (.signature owner "IxIR₁ papSafe declaration is not all-shared")
    else
      return signature

private def declarationSignature (context : Context)
    (declarations : List (Address × IxIR1.Decl)) (site : SourceSite)
    (address : Address) : Except Error Signature := do
  match sourceDeclAt? declarations address with
  | some (.fn definition) =>
      signatureOf context (.declaration address) address definition
  | some (.extern _) =>
      .error (.source site "compiler call expected a function declaration")
  | none => .error (.source site "call target is not declared")

private inductive BindingCap where
  | scalar
  | owned (world : Owned)
  | borrowed (world : Owned) (lender : BorrowLender)
  | dead
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

private structure Binding where
  atom : Atom
  cap : BindingCap
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

private abbrev SourceEnv := Array Binding

private structure Local where
  env : SourceEnv
  valueParams : Array ValueCap
  instructions : Array Instr := #[]
  nextValue : Nat

private def sourceAtom (site : SourceSite) (env : SourceEnv) :
    IxIR1.Atom → Except Error (Atom × BindingCap)
  | .lit literal => return (.lit literal, .scalar)
  | .erased => return (.erased, .scalar)
  | .var index =>
      match env[index]? with
      | none => .error (.source site s!"unbound IxIR₁ variable {index}")
      | some { cap := .dead, .. } =>
          .error (.ownership site s!"IxIR₁ variable {index} was already consumed")
      | some binding => return (binding.atom, binding.cap)

private def setDead (site : SourceSite) (env : SourceEnv) (index : Nat) :
    Except Error SourceEnv :=
  match env[index]? with
  | none => .error (.source site s!"unbound IxIR₁ variable {index}")
  | some binding => return env.setIfInBounds index { binding with cap := .dead }

private def consumeExpected (site : SourceSite) (expected : Owned)
    (env : SourceEnv) (source : IxIR1.Atom) :
    Except Error (SourceEnv × Atom) := do
  let (atom, capability) ← sourceAtom site env source
  match source, capability with
  | .lit _, .scalar | .erased, .scalar => return (env, atom)
  | .var _, .scalar => return (env, atom)
  | .var index, .owned world =>
      if world == expected then return (← setDead site env index, atom)
      else .error (.ownership site "operand has the wrong ownership world")
  | .var _, .borrowed .. =>
      .error (.ownership site "a borrowed value cannot cross an owned boundary")
  | _, .dead =>
      .error (.internal "dead source binding escaped sourceAtom")
  | _, _ => .error (.ownership site "invalid scalar capability")

private def consumeConcrete (site : SourceSite) (expected : Owned)
    (env : SourceEnv) (source : IxIR1.Atom) :
    Except Error (SourceEnv × ValueId) := do
  let (atom, capability) ← sourceAtom site env source
  match source, atom, capability with
  | .var index, .reg id, .owned world =>
      if world == expected then return (← setDead site env index, id)
      else .error (.ownership site "constructor operand has the wrong world")
  | .var _, _, .scalar =>
      .error (.ownership site "a concrete constructor location was required")
  | .var _, _, .borrowed .. =>
      .error (.ownership site "a borrowed constructor cannot be consumed")
  | _, _, _ =>
      .error (.ownership site "a concrete constructor register was required")

private def observeExpected (site : SourceSite) (expected : Owned)
    (env : SourceEnv) (source : IxIR1.Atom) : Except Error Atom := do
  let (atom, capability) ← sourceAtom site env source
  match capability with
  | .scalar => return atom
  | .owned world | .borrowed world _ =>
      if world == expected then return atom
      else .error (.ownership site "observed operand has the wrong world")
  | .dead => .error (.internal "dead source binding escaped sourceAtom")

private def requireScalar (site : SourceSite) (env : SourceEnv)
    (source : IxIR1.Atom) : Except Error Atom := do
  let (atom, capability) ← sourceAtom site env source
  match capability with
  | .scalar => return atom
  | _ => .error (.ownership site "extern operands must be statically scalar")

private def consumeArguments (site : SourceSite) (env : SourceEnv)
    (arguments : Array IxIR1.Atom) (worlds : Array Owned) :
    Except Error (SourceEnv × Array Atom) := do
  if arguments.size != worlds.size then
    .error (.source site "operand count does not match its ownership signature")
  else
    let (env, reversed) ←
      (arguments.toList.zip worlds.toList).foldlM (fun state pair => do
        let (env, atom) ← consumeExpected site pair.2 state.1 pair.1
        return (env, atom :: state.2)) (env, [])
    return (env, reversed.reverse.toArray)

private def consumeSharedArguments (site : SourceSite) (env : SourceEnv)
    (arguments : Array IxIR1.Atom) : Except Error (SourceEnv × Array Atom) :=
  consumeArguments site env arguments (Array.replicate arguments.size .shared)

private def bindResult (cursor : Local) (instruction : Instr)
    (capability : BindingCap) : Local :=
  { cursor with
    env := #[{ atom := .reg cursor.nextValue, cap := capability }] ++ cursor.env
    instructions := cursor.instructions.push instruction
    nextValue := cursor.nextValue + 1 }

private def bindEffect (cursor : Local) (instruction : Instr) : Local :=
  { cursor with
    env := #[{ atom := .erased, cap := .scalar }] ++ cursor.env
    instructions := cursor.instructions.push instruction }

private structure EdgeView where
  params : Array ValueCap
  arguments : Array Atom
  childEnv : SourceEnv

private def ownerParameter? (env : SourceEnv) (lender : ValueId) : Option Nat :=
  (List.range env.size).find? fun index =>
    match env[index]? with
    | some { atom := .reg id, cap := .owned _ } => id == lender
    | _ => false

private def edgeView (site : SourceSite) (env : SourceEnv) :
    Except Error EdgeView := do
  let rec go (index : Nat) (params : Array ValueCap)
      (arguments : Array Atom) (child : SourceEnv) : Except Error EdgeView :=
    if h : index < env.size then
      let binding := env[index]
      match binding.cap with
      | .dead =>
          go (index + 1) (params.push .scalar) (arguments.push .erased)
            (child.push { atom := .reg index, cap := .dead })
      | .scalar =>
          go (index + 1) (params.push .scalar) (arguments.push binding.atom)
            (child.push { atom := .reg index, cap := .scalar })
      | .owned world =>
          go (index + 1) (params.push (.owned world))
            (arguments.push binding.atom)
            (child.push { atom := .reg index, cap := .owned world })
      | .borrowed world .caller =>
          go (index + 1) (params.push (.borrowed world .caller))
            (arguments.push binding.atom)
            (child.push { atom := .reg index, cap := .borrowed world .caller })
      | .borrowed world (.value lender) =>
          match ownerParameter? env lender with
          | none =>
              .error (.ownership site "edge borrow has no transferred lender")
          | some targetLender =>
              go (index + 1)
                (params.push (.borrowed world (.value targetLender)))
                (arguments.push binding.atom)
                (child.push
                  { atom := .reg index
                    cap := .borrowed world (.value targetLender) })
    else
      return { params, arguments, childEnv := child }
  go 0 #[] #[] #[]

private def shiftAtom (amount : Nat) : Atom → Atom
  | .reg id => .reg (id + amount)
  | .lit literal => .lit literal
  | .erased => .erased

private def shiftLender (amount : Nat) : BorrowLender → BorrowLender
  | .caller => .caller
  | .value id => .value (id + amount)

private def shiftBinding (amount : Nat) (binding : Binding) : Binding :=
  { atom := shiftAtom amount binding.atom
    cap := match binding.cap with
      | .borrowed world lender => .borrowed world (shiftLender amount lender)
      | capability => capability }

private structure BuildState where
  blocks : Array (Option Block) := #[]
  scalarLeaves : List Validate.ScalarLeafFact := []
  positions : List PositionTrace := []
  edges : List EdgeTrace := []

private abbrev BuildM := EStateM Error BuildState

private def reserveBlock : BuildM BlockId := do
  let state ← get
  let id := state.blocks.size
  set { state with blocks := state.blocks.push none }
  return id

private def installBlock (id : BlockId) (block : Block) : BuildM Unit := do
  let state ← get
  match state.blocks[id]? with
  | some none => set { state with blocks := state.blocks.setIfInBounds id (some block) }
  | some (some _) => throw (.internal s!"block {id} was installed twice")
  | none => throw (.internal s!"block {id} was never reserved")

private def recordPosition (source : SourceSite) (block : BlockId)
    (target : TargetPosition) : BuildM Unit :=
  modify fun state =>
    { state with positions := { source, block, target } :: state.positions }

private def recordEdge (source : SourceSite) (sourceBlock target : BlockId)
    (view : EdgeView) (implicitScalars : Nat := 0) : BuildM Unit :=
  modify fun state =>
    { state with edges :=
        { source
          sourceBlock
          target
          explicitValues := view.arguments
          targetParams := view.params
          implicitScalars } :: state.edges }

private def recordScalarLeaf (owner : Validate.Owner) (block : BlockId)
    (value : ValueId) (cid : CtorId) : BuildM Unit :=
  modify fun state =>
    { state with scalarLeaves := { owner, block, value, cid } :: state.scalarLeaves }

private def lookupSchema (context : Context) (site : SourceSite)
    (world : Owned) (cid : CtorId) : BuildM CtorSchema :=
  match context.schemas world cid with
  | some schema => return schema
  | none => throw (.schema site "missing constructor schema")

private def liftExcept : Except Error α → BuildM α
  | .ok value => return value
  | .error error => throw error

private def lowerInstruction (context : Context)
    (declarations : List (Address × IxIR1.Decl)) (signature : Signature)
    (block : BlockId) (site : SourceSite) (cursor : Local)
    (operation : IxIR1.Op) : BuildM Local := do
  match operation with
  | .pure source =>
      let (atom, capability) ← liftExcept (sourceAtom site cursor.env source)
      let env ← match source, capability with
        | .var index, .owned _ => liftExcept (setDead site cursor.env index)
        | _, _ => pure cursor.env
      return (bindResult { cursor with env } (.move atom) capability)
  | .alloc world cid arguments =>
      let schema ← lookupSchema context site world cid
      let (env, atoms) ← liftExcept
        (consumeArguments site cursor.env arguments schema.fields)
      return bindResult { cursor with env } (.alloc world cid atoms) (.owned world)
  | .reuse .. =>
      throw (.unsupported site "raw IxIR₁ reuse is outside the baseline subset")
  | .free target =>
      let cid ← match context.scalarFreeCtor site with
        | some cid => pure cid
        | none => throw (.schema site "missing checked scalar-leaf free fact")
      let _ ← lookupSchema context site .unique cid
      let (env, value) ← liftExcept
        (consumeConcrete site .unique cursor.env target)
      recordScalarLeaf site.owner block value cid
      return bindEffect { cursor with env } (.freeUnique (.reg value) cid)
  | .dup target =>
      let (atom, capability) ← liftExcept (sourceAtom site cursor.env target)
      match capability with
      | .scalar =>
          return bindResult cursor (.retainShared atom) .scalar
      | .owned .shared | .borrowed .shared _ =>
          return bindResult cursor (.retainShared atom) (.owned .shared)
      | .owned .unique | .borrowed .unique _ =>
          throw (.ownership site "IxIR₁ dup requires a shared operand")
      | .dead => throw (.internal "dead source binding escaped sourceAtom")
  | .drop target =>
      let (env, atom) ← liftExcept
        (consumeExpected site .shared cursor.env target)
      return bindEffect { cursor with env } (.releaseShared atom)
  | .dropU target =>
      let (env, atom) ← liftExcept
        (consumeExpected site .unique cursor.env target)
      return bindEffect { cursor with env } (.dropUnique atom)
  | .fetch target field =>
      let cid ← match context.fetchCtor site with
        | some cid => pure cid
        | none => throw (.schema site "missing exact fetch constructor")
      let (atom, capability) ← liftExcept (sourceAtom site cursor.env target)
      let (world, lender) ← match capability, atom with
        | .owned world, .reg id => pure (world, BorrowLender.value id)
        | .borrowed world lender, _ => pure (world, lender)
        | .scalar, _ => throw (.ownership site "fetch requires a constructor")
        | .owned _, _ => throw (.internal "owned source binding is not a register")
        | .dead, _ => throw (.internal "dead source binding escaped sourceAtom")
      let schema ← lookupSchema context site world cid
      let fieldWorld ← match schema.fields[field]? with
        | some fieldWorld => pure fieldWorld
        | none => throw (.schema site s!"constructor field {field} is out of bounds")
      return bindResult cursor (.fetch atom cid field) (.borrowed fieldWorld lender)
  | .call address arguments =>
      let callee ← liftExcept
        (declarationSignature context declarations site address)
      let worlds := callee.params.map (fun parameter => parameter.world)
      let (env, atoms) ← liftExcept
        (consumeArguments site cursor.env arguments worlds)
      return bindResult { cursor with env } (.call address atoms)
        (.owned callee.result)
  | .callSelf arguments =>
      let worlds := signature.params.map (fun parameter => parameter.world)
      let (env, atoms) ← liftExcept
        (consumeArguments site cursor.env arguments worlds)
      return bindResult { cursor with env } (.callSelf atoms)
        (.owned signature.result)
  | .papp address arguments =>
      match sourceDeclAt? declarations address with
      | none => throw (.source site "partial-application target is not declared")
      | some (.extern arity) =>
          if !context.allowExtern then
            throw (.unsupported site "extern partial applications are disabled")
          else if arguments.size >= arity then
            throw (.source site "partial application is not under-saturated")
          else
            let atoms ← arguments.toList.mapM fun argument =>
              liftExcept (requireScalar site cursor.env argument)
            return bindResult cursor (.papp address atoms.toArray) (.owned .shared)
      | some (.fn _) =>
          let callee ← liftExcept
            (declarationSignature context declarations site address)
          if !callee.papSafe || arguments.size >= callee.params.size then
            throw (.source site "partial application target is not safely under-saturated")
          else
            let worlds := (callee.params.extract 0 arguments.size).map
              (fun parameter => parameter.world)
            let (env, atoms) ← liftExcept
              (consumeArguments site cursor.env arguments worlds)
            return bindResult { cursor with env } (.papp address atoms)
              (.owned .shared)
  | .apply function arguments =>
      let (env, function) ← liftExcept
        (consumeExpected site .shared cursor.env function)
      let (env, atoms) ← liftExcept
        (consumeSharedArguments site env arguments)
      return bindResult { cursor with env } (.apply function atoms)
        (.owned .shared)
  | .extern address arguments =>
      if !context.allowExtern then
        throw (.unsupported site "extern instructions are disabled")
      else
        match sourceDeclAt? declarations address with
        | some (.extern arity) =>
            if arguments.size != arity then
              throw (.source site "extern arity mismatch")
            else
              let atoms ← arguments.toList.mapM fun argument =>
                liftExcept (requireScalar site cursor.env argument)
              return bindResult cursor (.extern address atoms.toArray) .scalar
        | _ => throw (.source site "extern target is not an extern declaration")

private def initialEnv (signature : Signature) : SourceEnv :=
  let size := signature.params.size
  (List.range size).foldl (fun env sourceIndex =>
    let targetIndex := size - 1 - sourceIndex
    match signature.params[targetIndex]? with
    | some parameter =>
        env.push
          { atom := .reg targetIndex
            cap := match parameter.passing with
              | .owned => .owned parameter.world
              | .borrowed => .borrowed parameter.world .caller }
    | none => env) #[]

private def duplicateAltTag? : List IxIR1.Alt → Option Nat
  | [] => none
  | .mk tag _ _ :: rest =>
      if rest.any fun
          | .mk other _ _ => other == tag then some tag
      else duplicateAltTag? rest

private def altAtTag? (alternatives : Array IxIR1.Alt) (tag : Nat) :
    Option (IxIR1.Alt × Nat) :=
  alternatives.toList.zipIdx.find? fun pair =>
    match pair.1 with
    | .mk candidate _ _ => candidate == tag

private def finishBlocks (state : BuildState) : Except Error (Array Block) :=
  state.blocks.toList.mapM (fun (candidate : Option Block) =>
    match candidate with
    | some block => (Except.ok block : Except Error Block)
    | none => Except.error (Error.internal "reserved block was not installed"))
    |>.map List.toArray

private def compileFunction (context : Context)
    (declarations : List (Address × IxIR1.Decl)) (owner : Validate.Owner)
    (signature : Signature) (body : IxIR1.Code) :
    Except Error (Function × List Validate.ScalarLeafFact × Trace) :=
  let rec compile (fuel : Nat) (block : BlockId) (site : SourceSite)
      (cursor : Local) (code : IxIR1.Code) : BuildM Unit := do
    match fuel with
    | 0 => throw (.resources site)
    | fuel + 1 =>
      match code with
      | .ret source =>
          let (env, atom) ← liftExcept
            (consumeExpected site signature.result cursor.env source)
          recordPosition site block .terminator
          installBlock block
            { valueParams := cursor.valueParams
              creditParams := #[]
              instructions := cursor.instructions
              terminator := .ret atom }
          let _ := env
      | .letOp (.call address arguments) (.ret (.var 0)) =>
          match sourceDeclAt? declarations address with
          | some (.fn _) =>
              let callee ← liftExcept
                (declarationSignature context declarations site address)
              if callee.result == signature.result then
                let worlds := callee.params.map (fun parameter => parameter.world)
                let (_, atoms) ← liftExcept
                  (consumeArguments site cursor.env arguments worlds)
                recordPosition site block .terminator
                recordPosition site.next block .terminator
                installBlock block
                  { valueParams := cursor.valueParams
                    creditParams := #[]
                    instructions := cursor.instructions
                    terminator := .tailCall address atoms }
              else
                let index := cursor.instructions.size
                let cursor ← lowerInstruction context declarations signature block
                  site cursor (.call address arguments)
                recordPosition site block (.instruction index)
                compile fuel block site.next cursor (.ret (.var 0))
          | _ =>
              let index := cursor.instructions.size
              let cursor ← lowerInstruction context declarations signature block
                site cursor (.call address arguments)
              recordPosition site block (.instruction index)
              compile fuel block site.next cursor (.ret (.var 0))
      | .letOp (.callSelf arguments) (.ret (.var 0)) =>
          let worlds := signature.params.map (fun parameter => parameter.world)
          let (_, atoms) ← liftExcept
            (consumeArguments site cursor.env arguments worlds)
          recordPosition site block .terminator
          recordPosition site.next block .terminator
          installBlock block
            { valueParams := cursor.valueParams
              creditParams := #[]
              instructions := cursor.instructions
              terminator := .tailCallSelf atoms }
      | .letOp operation rest =>
          let index := cursor.instructions.size
          let cursor ← lowerInstruction context declarations signature block
            site cursor operation
          recordPosition site block (.instruction index)
          compile fuel block site.next cursor rest
      | .case scrutinee peelNat alternatives =>
          if let some tag := duplicateAltTag? alternatives.toList then
            throw (.source site s!"duplicate IxIR₁ case tag {tag}")
          let (_, scrutineeCap) ← liftExcept
            (sourceAtom site cursor.env scrutinee)
          let world ← match scrutineeCap with
            | .owned world | .borrowed world _ => pure world
            | .scalar => pure .shared
            | .dead => throw (.internal "dead source binding escaped sourceAtom")
          let view ← liftExcept (edgeView site cursor.env)
          let mut constructorTargets : Array CtorAlt := #[]
          for pair in alternatives.toList.zipIdx do
            let (.mk tag fieldCount altBody, altIndex) := pair
            match context.caseCtor site altIndex with
            | none =>
                if peelNat then pure ()
                else throw (.schema site
                  "non-Nat case alternative lacks a constructor identity")
            | some cid =>
                if cid.cidx != tag then
                  throw (.schema site "case constructor tag does not match IxIR₁")
                let schema ← lookupSchema context site world cid
                if schema.fields.size != fieldCount then
                  throw (.schema site "case field count does not match constructor schema")
                let child ← reserveBlock
                let childSite := site.alternative altIndex
                let (scrutinee, scrutineeCapability) ← liftExcept
                  (sourceAtom childSite view.childEnv scrutinee)
                let lender ← match scrutineeCapability, scrutinee with
                  | .owned _, .reg id => pure (BorrowLender.value id)
                  | .borrowed _ lender, _ => pure lender
                  | _, _ => throw (.ownership childSite "constructor arm lost its scrutinee")
                let mut childLocal : Local :=
                  { env := view.childEnv
                    valueParams := view.params
                    nextValue := view.params.size }
                let mut fields : SourceEnv := #[]
                for field in List.range fieldCount do
                  let fieldWorld := schema.fields[field]!
                  let resultId := childLocal.nextValue
                  childLocal :=
                    { childLocal with
                      instructions := childLocal.instructions.push
                        (.fetch scrutinee cid field)
                      nextValue := resultId + 1 }
                  fields := fields.push
                    { atom := .reg resultId
                      cap := .borrowed fieldWorld lender }
                childLocal :=
                  { childLocal with env := fields.reverse ++ childLocal.env }
                recordEdge site block child view
                compile fuel child childSite childLocal altBody
                constructorTargets := constructorTargets.push
                  { cid, edge := { target := child, values := view.arguments, credits := #[] } }
          let natPeel ← if peelNat then do
            let zero ← match altAtTag? alternatives 0 with
              | some (.mk _ 0 body, index) => pure (body, index)
              | _ => throw (.source site "Nat peel requires a nullary zero arm")
            let succ ← match altAtTag? alternatives 1 with
              | some (.mk _ 1 body, index) => pure (body, index)
              | _ => throw (.source site "Nat peel requires a unary successor arm")
            let zeroBlock ← reserveBlock
            let zeroSite := site.alternative zero.2
            recordEdge site block zeroBlock view
            compile fuel zeroBlock zeroSite
              { env := view.childEnv
                valueParams := view.params
                nextValue := view.params.size } zero.1
            let succBlock ← reserveBlock
            let succSite := site.alternative succ.2
            let shifted := view.childEnv.map (shiftBinding 1)
            let succEnv :=
              #[{ atom := .reg 0, cap := .scalar }] ++ shifted
            let succParams := #[.scalar] ++ view.params
            recordEdge site block succBlock
              { view with params := succParams } 1
            compile fuel succBlock succSite
              { env := succEnv
                valueParams := succParams
                nextValue := succParams.size } succ.1
            pure (some
              { zero := { target := zeroBlock, values := view.arguments, credits := #[] }
                succ := { target := succBlock, values := view.arguments, credits := #[] } })
          else
            pure none
          if constructorTargets.isEmpty && natPeel.isNone then
            throw (.source site "case has no translated alternatives")
          let (scrutinee, _) ← liftExcept (sourceAtom site cursor.env scrutinee)
          recordPosition site block .terminator
          installBlock block
            { valueParams := cursor.valueParams
              creditParams := #[]
              instructions := cursor.instructions
              terminator := .switchValue scrutinee constructorTargets natPeel }
  let action : BuildM Unit := do
    let entry ← reserveBlock
    if entry != 0 then throw (.internal "function entry block is not zero")
    let params := signature.params.map fun parameter =>
      match parameter.passing with
      | .owned => .owned parameter.world
      | .borrowed => .borrowed parameter.world .caller
    compile context.maxDepth entry { owner }
      { env := initialEnv signature
        valueParams := params
        nextValue := params.size } body
  match action.run {} with
  | .error error _ => .error error
  | .ok _ state => do
      let blocks ← finishBlocks state
      let trace : Trace :=
        { positions := state.positions.reverse
          edges := state.edges.reverse }
      return (⟨signature, blocks⟩, state.scalarLeaves.reverse, trace)

private def appendTrace (left right : Trace) : Trace :=
  { positions := left.positions ++ right.positions
    edges := left.edges ++ right.edges }

/-- Syntax-directed baseline lowering. This constructs all validator sidecars
that depend on target block/register identities, but does not hide validation;
use `lowerChecked` at an artifact boundary. -/
def lower (context : Context) (input : Input) : Except Error Artifact := do
  let _ ← match duplicateAddress? input.declarations with
    | some address => Except.error (.duplicateDeclaration address)
    | none => Except.ok ()
  let mut declarations : List (Address × Decl) := []
  let mut scalarLeaves : List Validate.ScalarLeafFact := []
  let mut trace : Trace := {}
  for entry in input.declarations do
    match entry.2 with
    | .extern arity =>
        declarations := declarations ++ [(entry.1, .extern arity)]
    | .fn definition =>
        let owner := Validate.Owner.declaration entry.1
        let signature ← signatureOf context owner entry.1 definition
        let (lowered, leaves, functionTrace) ←
          compileFunction context input.declarations owner signature definition.body
        declarations := declarations ++ [(entry.1, .fn lowered)]
        scalarLeaves := scalarLeaves ++ leaves
        trace := appendTrace trace functionTrace
  let mainSignature : Signature :=
    { params := #[], result := input.mainResult, papSafe := false }
  let (main, mainLeaves, mainTrace) ←
    compileFunction context input.declarations .main mainSignature input.main
  let validationContext : Validate.Context :=
    { schemas := context.schemas
      scalarLeaves := scalarLeaves ++ mainLeaves
      allowExtern := context.allowExtern }
  let artifact : Artifact :=
    { program := { declarations, main }
      validationContext
      trace := appendTrace trace mainTrace }
  return artifact

/-- Lower and immediately validate the exact artifact returned to the caller. -/
def lowerChecked (context : Context) (input : Input) : Except Error Checked := do
  let artifact ← lower context input
  match accepted : Validate.validate artifact.validationContext artifact.program with
  | .ok stats => return { artifact, stats, accepted }
  | .error error => .error (.validation error)

end Compilatrix.IxIR2.Lower
