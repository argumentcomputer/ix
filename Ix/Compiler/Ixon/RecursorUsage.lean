import Ix.Compiler.Ixon.UsageCheck

/-!
# Usage checking for saturated recursor rules

A recursor rule is entered with its complete parameter/field telescope.
Checking that telescope together avoids treating intermediate curried rule
lambdas as escaping closures. Bound callable parameters retain their syntactic
telescopes, so a known minor's unique result can feed a recursive call.
The original v0 checker is unchanged. This opt-in policy also permits a
definition's fully supplied entry telescope after its v0 check fails.
-/

namespace Ix.Compiler.Ixon.RecursorUsage

open UsageCheck

def policyTag : String := "recursor-modes/1"

structure Binding where
  world : Owned
  callable : Telescope := []

private def worlds (bindings : List Binding) : List Owned := bindings.map (·.world)

private def headTelescope (ctx : CheckCtx) (fuel : Nat) (bindings : List Binding)
    (head : Expr) : Except UsageErr Telescope :=
  match head with
  | .var index =>
      match bindings[index.toNat]? with
      | some binding => .ok binding.callable
      | none => .error (.unboundVar index.toNat)
  | _ => telescopeOfHead ctx fuel head

/-- A nullary constructor reference creates a new runtime cell. Its type has
no arrow on which to write a result world, so this explicit policy reconstructs
freshness from the resolved constructor declaration. -/
private def freshNullary (ctx : CheckCtx) (index : UInt64) : Bool :=
  (do
    let address ← ctx.refs[index.toNat]?
    let constant ← ctx.resolve address
    let .cPrj projection := constant.info | none
    let block ← ctx.resolve projection.block
    let .muts members := block.info | none
    let .indc inductiveType ← members[projection.idx.toNat]? | none
    let constructor ← inductiveType.ctors[projection.cidx.toNat]?
    return inductiveType.params == 0 && constructor.params == 0 && constructor.fields == 0
    : Option Bool).getD false

mutual

/-- The first-order body of a fully supplied rule. Unknown callable heads and
escaping closures are rejected; all ownership demands must be reconstructed. -/
def checkBody (ctx : CheckCtx) (fuel : Nat) (ghost : Bool)
    (bindings : List Binding) (expression : Expr) : Except UsageErr (UseVec × Owned) :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 => do
      let expression ← expandShareE ctx fuel expression
      match expression with
      | .app f a =>
          let (arguments, rawHead) := Expr.collectApp (.app f a)
          let head ← expandShareE ctx fuel rawHead
          let telescope ← headTelescope ctx fuel bindings head
          if arguments.length != telescope.length then
            throw (.internal "recursor mode rule requires a resolved saturated callable telescope")
          let (headUses, _) ← checkBody ctx fuel ghost bindings head
          let uses ← checkArguments ctx fuel ghost bindings telescope arguments headUses
          let result := if ghost then .shared else
            ((telescope[arguments.length - 1]?).map (·.owned)).getD .shared
          return (uses, result)
      | .lam .. | .letE .. | .prj .. | .all .. =>
          throw (.internal "recursor mode rule is outside the first-order body fragment")
      | .ref index _ =>
          if !ghost && freshNullary ctx index then
            return (UseVec.zeros bindings.length, .unique)
          else UsageCheck.check ctx fuel ghost (worlds bindings) expression
      | _ => UsageCheck.check ctx fuel ghost (worlds bindings) expression
  termination_by fuel

def checkArguments (ctx : CheckCtx) (fuel : Nat) (ghost : Bool)
    (bindings : List Binding) (telescope : Telescope) (arguments : List Expr)
    (accumulator : UseVec) : Except UsageErr UseVec :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 =>
      match arguments, telescope with
      | [], _ => .ok accumulator
      | _ :: _, [] => .error (.internal "recursor mode argument has no demand")
      | argument :: rest, demand :: demands => do
          let argument ← expandShareE ctx fuel argument
          let contribution ← if demand.dropped then do
            let (uses, _) ← UsageCheck.check ctx fuel true (worlds bindings) argument
            pure (UseVec.zeroScale uses)
          else do
            let (uses, actual) ← checkBody ctx fuel ghost bindings argument
            let unique := demand.uses == .linear || demand.uses == .affine
            if !ghost && unique && actual != .unique then throw (.dereliction demand.uses)
            if !ghost && !unique && actual == .unique then throw .freezeNeeded
            pure <| if !ghost && unique then
              match argument with
              | .var index => UseVec.singleMoved bindings.length index.toNat
              | _ => uses
            else uses
          checkArguments ctx fuel ghost bindings demands rest (UseVec.add accumulator contribution)
  termination_by fuel

end

private def validateUses : List (Uses × Bool) → UseVec → Except UsageErr Unit
  | [], [] => .ok ()
  | (mode, dropped) :: modes, use :: uses => do
      unless mode.covers use.uses do throw (.binderCovers mode use.uses)
      if dropped && use.uses != .erased then throw (.typeBinderRuntimeUse use.uses)
      if use.moved && use.uses != .linear then throw (.useAfterMove use.uses)
      validateUses modes uses
  | _, _ => .error (.internal "recursor rule usage telescope mismatch")

/-- Rule lambdas are an explicit saturated entry telescope, never a PAP.
Each retained binding stores its own type's callable demands. -/
def checkRule (ctx : CheckCtx) (fuel : Nat) (modes : List Uses) (result : Owned)
    (bindings : List Binding) (declared : List (Uses × Bool)) (body : Expr) :
    Except UsageErr Unit :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 => do
      let body ← expandShareE ctx fuel body
      match modes, body with
      | expected :: modes, .lam mode domain rest =>
          if mode != expected then
            throw (.internal "recursor rule binder disagrees with its source mode telescope")
          discard <| UsageCheck.check ctx fuel true (worlds bindings) domain
          let dropped := erasureDropsBinder ctx.sharing fuel mode domain
          checkRule ctx fuel modes result
            ({ world := worldOf mode, callable := telescopeOf ctx.sharing fuel domain } :: bindings)
            ((mode, dropped) :: declared) rest
      | [], body =>
          let (uses, actual) ← checkBody ctx fuel false bindings body
          if result == .unique && actual != .unique then throw (.resultNotUnique actual)
          if result != .unique && actual == .unique then throw .freezeNeeded
          validateUses declared uses
      | _, _ => throw (.internal "recursor mode rule does not match its complete telescope")
  termination_by fuel

/-- v1 is deliberately bounded to non-indexed unique-major recursors.
Their stored types remain the source of argument/result demands. -/
def checkRecursor (ctx : CheckCtx) (fuel : Nat) (recursor : Recursor) : Except UsageErr Unit := do
  let telescope := telescopeOf ctx.sharing fuel recursor.typ
  let some major := telescope.getLast? | throw (.internal "recursor mode telescope is empty")
  if worldOf major.uses != .unique then
    return ← UsageCheck.checkRecursor ctx fuel recursor
  if recursor.indices != 0 || recursor.motives != 0 || recursor.k then
    throw (.internal "unique recursor mode requires the non-indexed non-K fragment")
  if telescope.length != recursor.params.toNat + recursor.minors.toNat + 1 then
    throw (.internal "recursor mode telescope arity mismatch")
  discard <| UsageCheck.check ctx fuel true [] recursor.typ
  let parameterModes := (telescope.take (recursor.params.toNat + recursor.minors.toNat)).map (·.uses)
  for rule in recursor.rules do
    checkRule ctx fuel (parameterModes ++ List.replicate rule.fields.toNat .linear)
      major.owned [] [] rule.rhs

/-- A failed v0 definition may use the same bounded, fully supplied body
checker. This admits freshly constructed unique nullary values; it admits no
escaping lambda, let, projection, or unresolved callable body. -/
def checkDefinition (ctx : CheckCtx) (fuel : Nat) (definition : Definition) :
    Except UsageErr Unit := do
  discard <| UsageCheck.check ctx fuel true [] definition.typ
  let telescope := telescopeOf ctx.sharing fuel definition.typ
  checkRule ctx fuel (telescope.map (·.uses))
    ((telescope.getLast?).map (·.owned) |>.getD .shared) [] [] definition.value

/-- Explicit opt-in source policy. Definitions try v0 before the bounded
saturated entry rule; other non-recursor declarations retain v0 checks. -/
def checkConstant (resolve : Address → Option Constant) (constant : Constant)
    (fuel : Nat := UsageCheck.defaultFuel) : Except UsageErr Unit := do
  let members := match constant.info with | .muts members => members | _ => #[]
  let context : CheckCtx :=
    { resolve, sharing := constant.sharing, refs := constant.refs, selfMuts := members }
  match constant.info with
  | .defn definition =>
      match UsageCheck.checkDefinition resolve constant definition fuel with
      | .ok _ => pure ()
      | .error _ => checkDefinition context fuel definition
  | .recr recursor => checkRecursor context fuel recursor
  | .muts members =>
      for member in members do
        match member with
        | .recr recursor => checkRecursor context fuel recursor
        | .defn definition =>
            match UsageCheck.checkDefinition resolve constant definition fuel with
            | .ok _ => pure ()
            | .error _ => checkDefinition context fuel definition
        | .indc typeDefinition =>
            discard <| UsageCheck.check context fuel true [] typeDefinition.typ
            for constructor in typeDefinition.ctors do
              discard <| UsageCheck.check context fuel true [] constructor.typ
  | _ => UsageCheck.checkConstant resolve constant fuel

end Ix.Compiler.Ixon.RecursorUsage
