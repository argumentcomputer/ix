import Ix.Compiler.PipelineErasure
import Ix.Compiler.IxIR0.UniqueReverse

namespace Ix.Compiler.UniqueReuse

open Ix.Compiler.Ixon

structure RecursorWorlds where
  arguments : List Owned
  fields : List (List Owned)
  result : Owned
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

def recursorWorlds? (resolve : Address → Option Constant) (alias : Address)
    (fuel : Nat) : Option RecursorWorlds := do
  let constant ← resolve alias
  let .rPrj projection := constant.info | none
  let block ← resolve projection.block
  let .muts members := block.info | none
  let .recr recursor ← members[projection.idx.toNat]? | none
  if recursor.params != 0 || recursor.motives != 0 || recursor.indices != 0 || recursor.k then none else
    let telescope := UsageCheck.telescopeOf block.sharing fuel recursor.typ
    let result ← telescope.getLast?
    let fields := recursor.rules.toList.map fun rule =>
      ((Expr.collectLam rule.rhs).1.drop recursor.minors.toNat).map fun (mode, _) => UsageCheck.worldOf mode
    return { arguments := telescope.map fun demand => UsageCheck.worldOf demand.uses
             fields, result := result.owned }

def constructorWorlds? (resolve : Address → Option Constant) (address : Address)
    (fuel : Nat) : Option (Nat × List Owned × Owned) := do
  let constant ← resolve address
  let .cPrj projection := constant.info | none
  let block ← resolve projection.block
  let .muts members := block.info | none
  let .indc typeDefinition ← members[projection.idx.toNat]? | none
  let constructor ← typeDefinition.ctors[projection.cidx.toNat]?
  if constructor.params != 0 || typeDefinition.params != 0 then none else
    let telescope := UsageCheck.telescopeOf block.sharing fuel constructor.typ
    return (constructor.fields.toNat, telescope.map fun demand => UsageCheck.worldOf demand.uses,
      ((telescope.getLast?).map (·.owned)).getD .unique)

def builderWorlds? (resolve : Address → Option Constant) (address : Address)
    (fuel : Nat) : Option (List Owned × Owned) := do
  let constant ← resolve address
  let .defn definition := constant.info | none
  let telescope := UsageCheck.telescopeOf constant.sharing fuel definition.typ
  let result ← telescope.getLast?
  return (telescope.map fun demand => UsageCheck.worldOf demand.uses, result.owned)

structure ModeEvidence (resolve : Address → Option Constant)
    (schema : IxIR0.UniqueReverse.Schema) (fuel : Nat) : Prop where
  recursor : recursorWorlds? resolve schema.alias fuel =
    some { arguments := [.shared, .unique, .unique], fields := [[], [.unique, .unique]], result := .unique }
  nil : constructorWorlds? resolve schema.nil fuel = some (0, [], .unique)
  cons : constructorWorlds? resolve schema.cons fuel = some (2, [.unique, .unique], .unique)
  builder : builderWorlds? resolve schema.builder fuel = some ([.unique, .unique], .unique)

instance (resolve : Address → Option Constant) (schema : IxIR0.UniqueReverse.Schema)
    (fuel : Nat) : Decidable (ModeEvidence resolve schema fuel) :=
  decidable_of_iff
    (recursorWorlds? resolve schema.alias fuel =
        some { arguments := [.shared, .unique, .unique], fields := [[], [.unique, .unique]], result := .unique } ∧
      constructorWorlds? resolve schema.nil fuel = some (0, [], .unique) ∧
      constructorWorlds? resolve schema.cons fuel = some (2, [.unique, .unique], .unique) ∧
      builderWorlds? resolve schema.builder fuel = some ([.unique, .unique], .unique))
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩, fun h => ⟨h.recursor, h.nil, h.cons, h.builder⟩⟩

structure CheckedSource {constants : List (Address × Constant)} {entry : Pipeline.ClosedEntry}
    {config : Pipeline.Config} {checkFuel eraseFuel : Nat}
    (source : Pipeline.CertifiedErasure constants entry config .saturatedRecursorV1 .unique
      checkFuel eraseFuel) where
  recovery : IxIR0.UniqueReverse.Recovered source.erasure.result.raw source.rawMain
  modes : ModeEvidence (Pipeline.ResolverIndex.ofList constants).resolve recovery.checked.plan.schema checkFuel

def checkSource {constants : List (Address × Constant)} {entry : Pipeline.ClosedEntry}
    {config : Pipeline.Config} {checkFuel eraseFuel : Nat}
    (source : Pipeline.CertifiedErasure constants entry config .saturatedRecursorV1 .unique
      checkFuel eraseFuel) : Except String (CheckedSource source) := do
  let some recovery := IxIR0.UniqueReverse.recover source.erasure.result.raw source.rawMain
    | throw "unique reverse source is outside the checked specialization fragment"
  if hm : ModeEvidence (Pipeline.ResolverIndex.ofList constants).resolve recovery.checked.plan.schema checkFuel then
    return { recovery, modes := hm }
  else throw "unique reverse worlds do not match the original Ixon declarations"

end Ix.Compiler.UniqueReuse
