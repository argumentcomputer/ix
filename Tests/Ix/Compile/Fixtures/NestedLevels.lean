import Lean.Elab.BuiltinEvalCommand

/-!
Checked nested declarations whose occurrence levels have different raw
spellings and identical canonical serialized universes. `Mixed.Right`
mentions `List.{max 0 0}` and `List.{0}`; its equal-class neighbour uses
`List.{0}` twice. Either member as representative must discover one
canonical auxiliary. A/B reverse the source member order. Lean's source
auxiliary numbering remains source metadata, separate from canonical bytes.
-/

namespace Tests.Ix.Compile.Fixtures.NestedLevels

run_cmd Lean.Elab.Command.liftCoreM do
  let type : Lean.Expr := .sort (.succ .zero)
  for (family, changed) in [(`Mixed, true), (`Neighbour, false)] do
    for (presentation, reverse) in [(`A, false), (`B, true)] do
      let ns := `Tests.Ix.Compile.Fixtures.NestedLevels ++ family ++ presentation
      let left := ns ++ `Left
      let right := ns ++ `Right
      let list (owner : Lean.Name) (u : Lean.Level) : Lean.Expr :=
        .app (.const `List [u]) (.const owner [])
      let ctor (owner other : Lean.Name) (first : Lean.Level) : Lean.Constructor := {
        name := owner ++ `mk
        type := .forallE `x (list owner first)
          (.forallE `y (list owner .zero)
            (.forallE `r (.const other []) (.const owner []) .default) .default) .default }
      let members : List Lean.InductiveType :=
        [{ name := left, type, ctors := [ctor left right .zero] },
         { name := right, type, ctors := [ctor right left
             (if changed then .max .zero .zero else .zero)] }]
      Lean.addDecl <| .inductDecl [] 0 (if reverse then members.reverse else members) false

end Tests.Ix.Compile.Fixtures.NestedLevels
