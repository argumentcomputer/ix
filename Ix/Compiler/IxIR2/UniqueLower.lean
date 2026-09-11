import Ix.Compiler.UniqueReuse.Lower
import Ix.Compiler.IxIR2.Pipeline
import Ix.Compiler.IxIR2.Reuse

/-! A separate consuming translation rule for a checked unique recursor.
The ordinary lowerer's non-scalar shallow-free rejection remains intact.
Here the complete case/field/free shape is known: `takeUnique` transfers every
field, and `discardCredit` implements the original shallow free. Every output
crosses the ordinary call-local v0 validator before optional static reuse. -/

namespace Ix.Compiler.IxIR2.UniqueLower

open Ix.Compiler.Ixon (Owned)
open Ix.Compiler.IxIR0.UniqueReverse (Schema Plan)
open Ix.Compiler.UniqueReuse (nilId consId functionAddress)

def policyTag : String := "consuming-unique-recursor/1"
def reusePolicyTag : String := "static-unique-reuse/1"

def schemas (schema : Schema) : Owned → CtorId → Option CtorSchema
  | .unique, identity =>
      if identity == nilId schema then
        some { layout := Pipeline.baselineLayout .unique identity, fields := #[] }
      else if identity == consId schema then
        some { layout := Pipeline.baselineLayout .unique identity, fields := #[.unique, .unique] }
      else none
  | .shared, _ => none

def signature : Signature :=
  { params := #[{ world := .unique, passing := .owned }, { world := .unique, passing := .owned }]
    result := .unique, papSafe := false }

def entryBlock (schema : Schema) : Block :=
  { valueParams := #[.owned .unique, .owned .unique], creditParams := #[], instructions := #[]
    terminator := .switchValue (.reg 1) #[
      { cid := nilId schema, edge := { target := 1, values := #[.reg 0, .reg 1], credits := #[] } },
      { cid := consId schema, edge := { target := 2, values := #[.reg 0, .reg 1], credits := #[] } }] none }

def nilBlock (schema : Schema) : Block :=
  { valueParams := #[.owned .unique, .owned .unique], creditParams := #[]
    instructions := #[.takeUnique (.reg 1) (nilId schema), .discardCredit 0]
    terminator := .ret (.reg 0) }

def consBlock (schema : Schema) (reuse : Bool) : Block :=
  { valueParams := #[.owned .unique, .owned .unique], creditParams := #[]
    instructions := #[.takeUnique (.reg 1) (consId schema)] ++
      (if reuse then #[.allocWith 0 .unique (consId schema) #[.reg 2, .reg 0]]
       else #[.discardCredit 0, .alloc .unique (consId schema) #[.reg 2, .reg 0]])
    terminator := .tailCallSelf #[.reg 4, .reg 3] }

def function (schema : Schema) (reuse : Bool) : Function :=
  { signature, blocks := #[entryBlock schema, nilBlock schema, consBlock schema reuse] }

def inputInstructions (plan : Plan) : Array Instr :=
  #[.alloc .unique (nilId plan.schema) #[]] ++
    (plan.values.reverse.mapIdx fun index value =>
      .alloc .unique (consId plan.schema) #[.lit (.nat value), .reg index]).toArray ++
    #[.alloc .unique (nilId plan.schema) #[]]

def mainFunction (plan : Plan) : Function :=
  { signature := { params := #[], result := .unique, papSafe := false }
    blocks := #[
      { valueParams := #[], creditParams := #[], instructions := inputInstructions plan
        terminator := .tailCall (functionAddress plan.schema)
          #[.reg (plan.values.length + 1), .reg plan.values.length] }] }

def program (plan : Plan) (reuse : Bool) : Program :=
  { declarations := [(functionAddress plan.schema, .fn (function plan.schema reuse))]
    main := mainFunction plan }

def context (schema : Schema) : Validate.Context := { schemas := schemas schema }

def input (plan : Plan) : Lower.Input :=
  { declarations := Ix.Compiler.UniqueReuse.declarations plan.schema
    main := Ix.Compiler.UniqueReuse.mainCode plan, mainResult := .unique }

structure Translation (source : Lower.Input) (plan : Plan) (limits : Validate.Limits) where
  sourceEq : source = input plan
  checked : Validate.Checked limits (context plan.schema) (program plan false)

def translate (plan : Plan) (limits : Validate.Limits := Validate.defaultLimits) :
    Except String (Translation (input plan) plan limits) :=
  match hc : Validate.validateWith limits (context plan.schema) (program plan false) with
  | .error error => .error s!"consuming target rejected: {repr error}"
  | .ok stats => .ok { sourceEq := rfl, checked := { stats, accepted := hc } }

inductive Skip where
  | disabled
  | rewriteBudget
  | liveness (detail : String)
  | layout
  | validation (error : Validate.Error)
  deriving Repr

structure ReusePolicy where
  enabled : Bool := true
  maxRewrites : Nat := 1
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

inductive Selection (plan : Plan) (limits : Validate.Limits) where
  | baseline (reason : Skip) (checked : Validate.Checked limits (context plan.schema) (program plan false))
  | optimized (placement : Reuse.Placement (consBlock plan.schema false))
      (valueEq : placement.value = 1) (positionEq : placement.position = 0)
      (checked : Validate.Checked limits (context plan.schema) (program plan true))

def Selection.reused {plan : Plan} {limits : Validate.Limits} : Selection plan limits → Bool
  | .baseline .. => false
  | .optimized .. => true

def Selection.program {plan : Plan} {limits : Validate.Limits} (selection : Selection plan limits) : Program :=
  UniqueLower.program plan selection.reused

def Selection.checked {plan : Plan} {limits : Validate.Limits} (selection : Selection plan limits) :
    Validate.Checked limits (context plan.schema) selection.program := by
  cases selection with
  | baseline _ checked => exact checked
  | optimized _ _ _ checked => exact checked

/-- The source instance fixes both constructors of this reuse site. Liveness
still certifies the actual consumed register, and complete validation checks
the target credit and field transfers. Any optional failure retains the exact
checked consuming baseline. -/
def select (plan : Plan) (limits : Validate.Limits)
    (baseline : Validate.Checked limits (context plan.schema) (program plan false))
    (policy : ReusePolicy := {}) : Selection plan limits :=
  if !policy.enabled then .baseline .disabled baseline
  else if policy.maxRewrites == 0 then .baseline .rewriteBudget baseline
  else match hp : Reuse.inferPlacementWith limits (consBlock plan.schema false) 1 0 with
    | .error error => .baseline (.liveness s!"{repr error}") baseline
    | .ok none => .baseline (.liveness "unique source has a later use") baseline
    | .ok (some placement) =>
        have hm := Reuse.inferPlacementWith_sound hp
        match schemas plan.schema .unique (consId plan.schema) with
        | none => .baseline .layout baseline
        | some _ =>
            match hc : Validate.validateWith limits (context plan.schema) (program plan true) with
            | .error error => .baseline (.validation error) baseline
            | .ok stats => .optimized placement hm.1 hm.2 { stats, accepted := hc }

end Ix.Compiler.IxIR2.UniqueLower
