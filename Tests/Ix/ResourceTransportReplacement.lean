import Ix.Resource.Transport.Prepare

/- Synthetic traversal controls only. Real replacement eligibility and the
checked equation RHS are exercised separately by combined-addressed tests. -/
namespace Tests.ResourceTransportReplacement
open Ix.Resource Ixon
def r (i : UInt64) : Ixon.Expr := .ref i #[]
def fn : Ixon.Expr := .all { value := .unique } .unique (r 0) (r 0)
def bad : Ixon.Expr := .lam { value := .unique } (r 0) (r 1)
def good : Ixon.Expr := .lam { value := .unique } (r 0) (.var 0)
def p : Program := {
  propSort := some 1
  declarations := #[
    { type := .sort 0, kind := .assumption },
    { type := r 0, kind := .assumption },
    { type := .sort 1, kind := .assumption },
    { type := .all .many .shared fn (r 2), kind := .assumption },
    { type := .all .many .shared fn fn, kind := .assumption },
    { type := .all .many .shared fn (r 0), kind := .constructor },
    { type := .all { uses := .erased } .shared fn (r 0), kind := .assumption }] }
def m : Transport.Metadata := {
  universes := #[.succ .zero, .zero]
  kinds := p.declarations.map fun _ => .axiomDecl false
  levelArities := Array.replicate p.declarations.size 0
  resourceSensitive := (Transport.resourceSensitivity p p {}).toOption.getD #[] }
def run : IO UInt32 := do
  let mut failures := 0
  for (name, term, type, headers, accept) in #[
      ("explicit bad callback", bad, fn, 0, false),
      ("explicit honest callback", good, fn, 0, true),
      ("hidden proof witness", .app (r 3) bad, r 2, 0, false),
      ("honest proof witness", .app (r 3) good, r 2, 0, true),
      ("indirect callback argument", .app (r 4) bad, fn, 0, false),
      ("constructor callback field", .app (r 5) bad, r 0, 0, false),
      ("erased callback argument", .app (r 6) bad, r 0, 0, false),
      ("let callback alias", .leanLet false fn bad (.var 0), fn, 0, false),
      ("extra bad lambda after public header", .lam .many (r 0) bad,
        .all .many .shared (r 0) fn, 1, false),
      ("extra honest lambda after public header", .lam .many (r 0) good,
        .all .many .shared (r 0) fn, 1, true)] do
    let result := Transport.runTyping m {} <|
      Transport.check m p 256 { program := p } term type (.replacement headers)
    let pass := result.toOption.isSome == accept
    IO.println s!"{if pass then "PASS" else "FAIL"} {name}: {repr result}"
    unless pass do failures := failures + 1
  return if failures == 0 then 0 else 1
end Tests.ResourceTransportReplacement
