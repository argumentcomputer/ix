import Ix.Compiler.UniqueReuse.Sources
import Ix.Compiler.UniqueReuse.ModeCheck

/-! A checked source function with one owned list argument. Its constants and
entry contain no input payloads. The closed expression names the function;
runtime application is a separate semantic operation. -/

namespace Ix.Compiler.UniqueReuse.Runtime

open Ix.Compiler.Ixon (Address Constant)
open Ix.Compiler.IxIR0.UniqueReverse (Schema SourceMatches)

def policyTag : String := "unique-reverse-runtime/1"

structure Source where
  constants : List (Address × Constant)
  root : Address
  dataBlock : Address
  nil : Address
  cons : Address

def Source.entry (source : Source) : Pipeline.ClosedEntry :=
  { refs := #[source.root], univs := #[.zero], source := .ref 0 #[] }

/-- Reuse the accepted unique constructor and recursor declarations, replacing
only the closed fixture entry with `fun xs => reverseOnto nil xs`. -/
def source : Except String Source := do
  let base ← Examples.source []
  let listType := (base.constants.find? fun pair => match pair.2.info with
    | .iPrj projection => projection.idx == 1 && projection.block == base.dataBlock
    | _ => false).map (·.1)
  let some listType := listType | throw "unique list type projection is missing"
  let body : Ixon.Expr := .app
    (.app (.app (.ref 0 #[]) (.ref 3 #[])) (.ref 1 #[])) (.var 0)
  let entry ← Coverage.addressed
    { info := .defn
        { kind := .defn, safety := .safe, lvls := 0
          typ := .all .linear .unique (.ref 4 #[]) (.ref 4 #[])
          value := .lam .linear (.ref 4 #[]) body }
      sharing := #[], refs := #[base.recursor, base.nil, base.cons, base.builder, listType]
      univs := #[.zero] }
  return { constants := base.constants.filter (fun pair => pair.1 != base.root) ++ [entry],
           root := entry.1, dataBlock := base.dataBlock, nil := base.nil, cons := base.cons }

def body (schema : Schema) : IxIR0.Expr :=
  IxIR0.UniqueReverse.literalCall schema (.var 0) (.ref schema.nil)

structure SourceShape (declarations : List (Address × IxIR0.Decl)) (main : IxIR0.Expr) where
  schema : Schema
  root : Address
  mainEq : main = .ref root
  declarationsAt : SourceMatches (IxIR0.Env.ofList declarations) schema
  entry : IxIR0.Env.ofList declarations root = some (.defn .unique (.lam .linear (body schema)))

def recognize (declarations : List (Address × IxIR0.Decl)) (main : IxIR0.Expr) :
    Option (SourceShape declarations main) := do
  let .ref root := main | none
  let env := IxIR0.Env.ofList declarations
  let some (.defn .unique (.lam .linear
      (.app (.app (.app (.ref alias) (.ref builder)) (.ref nil)) (.var 0)))) := env root | none
  let some (.defn .shared (.ref recursor)) := env alias | none
  let some (.defn .unique (.lam .linear (.lam .linear
      (.app (.app (.ref cons) (.var 1)) (.var 0))))) := env builder | none
  let schema : Schema := { nil, cons, alias, recursor, builder }
  if hm : SourceMatches env schema then
    if he : env root = some (.defn .unique (.lam .linear (body schema))) then
      if hmain : main = .ref root then
        some { schema, root, mainEq := hmain, declarationsAt := hm, entry := he }
      else none
    else none
  else none

structure CheckedSource {constants : List (Address × Constant)} {entry : Pipeline.ClosedEntry}
    {config : Pipeline.Config} {checkFuel eraseFuel : Nat}
    (erased : Pipeline.CertifiedErasure constants entry config .saturatedRecursorV1 .shared checkFuel eraseFuel) where
  shape : SourceShape erased.erasure.result.raw erased.rawMain
  modes : ModeEvidence (Pipeline.ResolverIndex.ofList constants).resolve shape.schema checkFuel
  argumentMode : builderWorlds? (Pipeline.ResolverIndex.ofList constants).resolve shape.root checkFuel =
    some ([.unique], .unique)

def checkSource {constants : List (Address × Constant)} {entry : Pipeline.ClosedEntry}
    {config : Pipeline.Config} {checkFuel eraseFuel : Nat}
    (erased : Pipeline.CertifiedErasure constants entry config .saturatedRecursorV1 .shared checkFuel eraseFuel) :
    Except String (CheckedSource erased) := do
  let some shape := recognize erased.erasure.result.raw erased.rawMain
    | throw "runtime reverse requires the checked one-argument source function"
  let resolve := (Pipeline.ResolverIndex.ofList constants).resolve
  if hm : ModeEvidence resolve shape.schema checkFuel then
    if ha : builderWorlds? resolve shape.root checkFuel = some ([.unique], .unique) then
      return { shape, modes := hm, argumentMode := ha }
    else throw "runtime reverse entry must consume one unique list and return a unique list"
  else throw "runtime reverse constructor and recursor worlds do not match"

end Ix.Compiler.UniqueReuse.Runtime
