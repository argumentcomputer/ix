module
public import Ix.Resource.Transport.Prepare

public section
namespace Tests.ResourceTransport
open Ix.Resource Ixon

private def ref (n : UInt64) : Ixon.Expr := .ref n #[]
private def var (n : UInt64) : Ixon.Expr := .var n
private def arr (a b : Ixon.Expr) : Ixon.Expr := .all .many .shared a b
private def apps (f : Ixon.Expr) (xs : List Ixon.Expr) : Ixon.Expr :=
  xs.foldl Ixon.Expr.app f
private def ty : Ixon.Expr := .sort 0
private def prop : Ixon.Expr := .sort 1
private def eq (head : UInt64) (a x y : Ixon.Expr) : Ixon.Expr :=
  apps (ref head) [a, x, y]
private def eqTy : Ixon.Expr := arr (.sort 2) (arr (var 0) (arr (var 1) prop))
private def reflTy (head : UInt64) : Ixon.Expr :=
  arr (.sort 2) (arr (var 0) (eq head (var 1) (var 0) (var 0)))
private def transportTy (head : UInt64) : Ixon.Expr :=
  arr ty (arr ty (arr (eq head ty (var 1) (var 0)) (arr (var 2) (var 2))))
private def sharedFn : Ixon.Expr := arr (ref 0) (ref 0)
private def uniqueFn : Ixon.Expr := .all .many .unique (ref 0) (ref 0)
private def uniqueInputFn : Ixon.Expr :=
  .all { value := .unique } .shared (ref 0) (ref 0)
private def genericBody : Ixon.Expr :=
  .lam .many ty (.lam .many ty
    (.lam .many (eq 4 ty (var 1) (var 0))
      (.lam .many (var 2) (apps (ref 6) [var 3, var 2, var 1, var 0]))))
private def decl (type : Ixon.Expr) (body : Option Ixon.Expr := none) : Declaration :=
  { type, body, kind := if body.isSome then .definition else .assumption }

/-- Synthetic interfaces isolate typing-filter behavior. The assumptions
are deliberately explicit; this is NOT primitive structural validation. -/
def program : Program := {
  propSort := some 1
  declarations := #[
    decl ty,                                -- 0 abstract ordinary data
    decl ty,                                -- 1 unused data
    decl ty (some sharedFn),                 -- 2 shared alias
    decl ty (some uniqueFn),                 -- 3 unique alias
    decl eqTy,                              -- 4 Eq
    decl (reflTy 4),                         -- 5 Eq.refl
    decl (transportTy 4),                    -- 6 cast primitive
    decl sharedFn (some (.lam .many (ref 0) (var 0))), -- 7 shared identity
    decl (transportTy 4) (some genericBody),  -- 8 generic wrapper
    decl eqTy,                              -- 9 fresh indexed equality
    decl (reflTy 9),                         -- 10 custom reflexivity
    decl (transportTy 9),                    -- 11 custom eliminator
    decl (arr ty ty) (some (.lam .many ty (var 0))), -- 12 type-valued id
    decl prop,                              -- 13 True
    decl (ref 13),                          -- 14 True.intro
    decl (arr ty prop),                     -- 15 Nonempty
    decl (arr ty (arr (var 0) (.app (ref 15) (var 1)))), -- 16 Nonempty.intro
    decl (ref 0)                            -- 17 shared data constant
  ]
}

private def refl (head : UInt64) (a : Ixon.Expr) : Ixon.Expr := apps (ref head) [ty, a]
private def cast (head : UInt64) (a b h value : Ixon.Expr) : Ixon.Expr :=
  apps (ref head) [a, b, h, value]

structure Case where
  name : String
  term : Ixon.Expr
  expected : Ixon.Expr
  accept : Bool

def cases : Array Case := #[
  ⟨"direct shared-to-unique", cast 6 sharedFn uniqueFn (refl 5 sharedFn) (ref 7), uniqueFn, false⟩,
  ⟨"alias laundering", cast 6 (ref 2) (ref 3) (refl 5 (ref 2)) (ref 7), uniqueFn, false⟩,
  ⟨"unique-input contract changed", cast 6 sharedFn uniqueInputFn (refl 5 sharedFn) (ref 7), uniqueInputFn, false⟩,
  ⟨"generic wrapper laundering", cast 8 sharedFn uniqueFn (refl 5 sharedFn) (ref 7), uniqueFn, false⟩,
  ⟨"custom indexed equality", cast 11 sharedFn uniqueFn (refl 10 sharedFn) (ref 7), uniqueFn, false⟩,
  ⟨"same-type transport control", cast 6 sharedFn sharedFn (refl 5 sharedFn) (ref 7), sharedFn, true⟩,
  ⟨"generic proof-parameter control", genericBody, transportTy 4, true⟩,
  ⟨"type-valued beta laundering",
    cast 6 (.app (ref 12) sharedFn) (.app (ref 12) uniqueFn)
      (refl 5 (.app (ref 12) sharedFn)) (ref 7), uniqueFn, false⟩,
  ⟨"type-valued beta control",
    cast 6 (.app (ref 12) sharedFn) sharedFn
      (refl 5 (.app (ref 12) sharedFn)) (ref 7), sharedFn, true⟩,
  ⟨"uncovered dishonest result promise", .lam .many (ref 0) (var 0), uniqueFn, false⟩,
  ⟨"bad computational witness inside Nonempty",
    apps (ref 16) [uniqueFn, .lam .many (ref 0) (ref 17)], .app (ref 15) uniqueFn, false⟩,
  ⟨"valid annotated Prop telescope", .lam { uses := .linear } (ref 0) (ref 14),
    .all { uses := .linear } .shared (ref 0) (ref 13), true⟩,
  ⟨"computational witness captures linear proof-telescope parameter",
    .lam { uses := .linear } (ref 0)
      (apps (ref 16) [sharedFn, .lam .many (ref 0) (var 1)]),
    .all { uses := .linear } .shared (ref 0) (.app (ref 15) sharedFn), false⟩
]

def metadata (p : Program) : Transport.Metadata := {
  universes := #[.succ .zero, .zero, .succ (.succ .zero)]
  kinds := p.declarations.map fun d => if d.body.isSome then .definition else .axiomDecl false
  levelArities := Array.replicate p.declarations.size 0
  resourceSensitive := (Transport.resourceSensitivity p p {}).toOption.getD #[] }

def run : IO UInt32 := do
  let m := metadata program
  let mut failures := 0
  for test in cases do
    let result := Transport.runTyping m {} (Transport.check m program 256 { program } test.term test.expected .uncovered)
    let accepted := result.toOption.isSome
    unless accepted == test.accept do failures := failures + 1
    IO.println s!"{if accepted == test.accept then "PASS" else "FAIL"} {test.name}: {repr result}"
  let opposite := Transport.runTyping m {} (Transport.compatible m program 256 { program } ty prop)
  IO.println s!"opposite sorts: {repr opposite}"
  unless opposite.toOption == some false do failures := failures + 1
  let overridden := { program with interfaces := #[(7, uniqueFn)] }
  let overrideResult := Transport.runTyping m {} (Transport.check m overridden 256 { program } (ref 7) uniqueFn .uncovered)
  IO.println s!"source type resists runtime override: {repr overrideResult}"
  if overrideResult.toOption.isSome then failures := failures + 1
  let keepType : Ixon.Expr := .all { value := .unique } .unique (ref 0) (ref 0)
  let keepBody : Ixon.Expr := .lam { value := .unique } (ref 0) (var 0)
  let withKeep := { program with declarations := program.declarations.push (decl keepType (some keepBody)) }
  let resources := checkDefinitionCrossed withKeep program.declarations.size
  let checked := resources.bind fun _ => Transport.runTyping (metadata withKeep) {}
    (Transport.check (metadata withKeep) withKeep 256 { program := withKeep } keepBody keepType .runtime)
  IO.println s!"genuine runtime unique identity: {repr checked}"
  unless checked.toOption.isSome do failures := failures + 1
  let primitive : Program := { declarations := #[{ type := ty, kind := .typeConstructor }] }
  let primitiveMeta : Transport.Metadata := {
    universes := m.universes, levelArities := #[0], kinds := #[.inductiveType]
    inductives := #[{ index := 0, params := 0, indices := 0, constructors := #[] }] }
  for (name, info, roots, accept) in #[
      ("safe primitive fragment", primitiveMeta, #[0], true),
      ("unsafe selected primitive", { primitiveMeta with unsafePrimitives := #[0] }, #[0], false),
      ("unsafe unselected primitive", { primitiveMeta with unsafePrimitives := #[0] }, #[], true)] do
    let result := Transport.validate primitive primitive info { roots }
    let pass := result.toOption.isSome == accept
    IO.println s!"{if pass then "PASS" else "FAIL"} {name}: {repr result}"
    unless pass do failures := failures + 1
  for (level, accept) in #[(0, true), (1, false)] do
    let lhs := Ixon.Expr.ref 0 #[level]
    let p : Program := { declarations := #[
      decl (.sort 0), decl (eq 2 (.sort 0) lhs lhs), decl (.sort 0)] }
    let info : Transport.Metadata := {
      universes := #[.var 0, .zero], levelArities := #[1, 1, 0], eqType := some 2 }
    let result := Transport.runTyping info {} (Transport.validateEquation p p info 256 0 1)
    let pass := result.toOption.isSome == accept
    IO.println s!"{if pass then "PASS" else "FAIL"} equation universe {level}: {repr result}"
    unless pass do failures := failures + 1
  IO.println s!"{failures} failures"
  return if failures == 0 then 0 else 1

end Tests.ResourceTransport
end
