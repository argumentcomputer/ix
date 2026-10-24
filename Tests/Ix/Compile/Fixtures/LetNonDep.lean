import Lean.Elab.BuiltinEvalCommand

/-!
Checked source declarations for the serialized `letE.nonDep` key. Surface
`let` and `have` elaborate to the same flag here, so `addDecl` preserves the
two legal raw spellings while the ordinary Lean kernel checks every declaration.

`Split` differs only in the flag and must have two canonical classes.
`Equal` keeps the flag and changes binder spelling, so it must collapse.
Each has a reversed member-order presentation. Canonical payload bytes are
compared separately from the source-order metadata.
-/

namespace Tests.Ix.Compile.Fixtures.LetNonDep

run_cmd Lean.Elab.Command.liftCoreM do
  let type : Lean.Expr := .sort (.succ .zero)
  let value (binder : Lean.Name) (nd : Bool) : Lean.Expr :=
    .letE binder type (.sort .zero) (.bvar 0) nd
  for (name, binder, nd) in
      [(`Tests.Ix.Compile.Fixtures.LetNonDep.letForm, `a, false),
       (`Tests.Ix.Compile.Fixtures.LetNonDep.haveForm, `a, true),
       (`Tests.Ix.Compile.Fixtures.LetNonDep.neighbour, `b, false)] do
    Lean.addDecl <| .defnDecl {
      name, levelParams := [], type, value := value binder nd,
      hints := .abbrev, safety := .safe }
  for (family, rightFlag) in [(`Split, true), (`Equal, false)] do
    for (presentation, reverse) in [(`A, false), (`B, true)] do
      let ns := `Tests.Ix.Compile.Fixtures.LetNonDep ++ family ++ presentation
      let left := ns ++ `Left
      let right := ns ++ `Right
      let ctor (owner other binder : Lean.Name) (nd : Bool) : Lean.Constructor := {
        name := owner ++ `mk
        type := .forallE `p (value binder nd)
          (.forallE `r (.const other []) (.const owner []) .default) .default }
      let members : List Lean.InductiveType :=
        [{ name := left, type, ctors := [ctor left right `a false] },
         { name := right, type, ctors := [ctor right left `b rightFlag] }]
      Lean.addDecl <| .inductDecl [] 0 (if reverse then members.reverse else members) false

end Tests.Ix.Compile.Fixtures.LetNonDep
