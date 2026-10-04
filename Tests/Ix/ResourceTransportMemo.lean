import Ix.Resource.Transport.Prepare
namespace Tests.ResourceTransportMemo
open Ix.Resource Ixon
def r (i : UInt64) : Ixon.Expr := .ref i #[]
def fn : Ixon.Expr := .all { value := .unique } .unique (r 0) (r 0)
def sharedFn : Ixon.Expr := .all .many .shared (r 0) (r 0)
def bad : Ixon.Expr := .lam { value := .unique } (r 0) (r 1)
def capture : Ixon.Expr := .lam .many (r 0) (.var 1)
def p : Program := {
  propSort := some 1, sharing := #[.sort 2]
  declarations := #[{ type := .sort 0, kind := .assumption },
    { type := r 0, kind := .assumption }] }
def m : Transport.Metadata := {
  universes := #[.succ .zero, .zero, .var 0]
  kinds := #[.axiomDecl false, .axiomDecl false], levelArities := #[0, 0]
  resourceSensitive := (Transport.resourceSensitivity p p {}).toOption.getD #[] }
def run : IO UInt32 := do
  let ctx : Context := { program := p }
  let coverage : CheckM Unit := do
    Transport.check m p 256 ctx bad fn .runtime
    Transport.check m p 256 ctx bad fn .uncovered
  let contracts : CheckM Unit := do
    Transport.underBinder ctx .many (r 0) fun inner =>
      Transport.check m p 256 inner capture sharedFn .uncovered
    Transport.underBinder ctx { value := .unique } (r 0) fun inner =>
      Transport.check m p 256 inner capture sharedFn .uncovered
  let order : CheckM Unit := do
    Transport.underBinder ctx .many (r 0) fun first =>
      Transport.underBinder first .many fn fun inner =>
        Transport.check m p 256 inner (.var 0) fn .runtime
    Transport.underBinder ctx .many fn fun first =>
      Transport.underBinder first .many (r 0) fun inner =>
        Transport.check m p 256 inner (.var 0) fn .runtime
  let expected : CheckM Unit :=
    Transport.underBinder ctx .many fn fun inner => do
      Transport.check m p 256 inner (.var 0) fn .runtime
      Transport.check m p 256 inner (.var 0) sharedFn .runtime
  let universes : CheckM Unit := do
    let a ← Transport.instantiateLevels p #[.zero] 256 (.share 0)
    let b ← Transport.instantiateLevels p #[.succ .zero] 256 (.share 0)
    let .sort ua := a | throw .typeMismatch
    let .sort ub := b | throw .typeMismatch
    unless (← Transport.universeZero 256 ua) && !(← Transport.universeZero 256 ub) do
      throw .typeMismatch
  let mut failures := 0
  for (name, action, accept) in #[
      ("coverage mode is part of the key", coverage, false),
      ("outer ownership contract is part of the key", contracts, false),
      ("binder type and order are part of the key", order, false),
      ("expected contract is part of the key", expected, false),
      ("sharing remains universe-instance-specific", universes, true)] do
    let result := Transport.runTyping m {} action
    let pass := result.toOption.isSome == accept
    IO.println s!"{if pass then "PASS" else "FAIL"} {name}: {repr result}"
    unless pass do failures := failures + 1
  return if failures == 0 then 0 else 1
end Tests.ResourceTransportMemo
