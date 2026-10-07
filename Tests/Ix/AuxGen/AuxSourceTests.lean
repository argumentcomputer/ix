module

public import LSpec
public import Ix.AuxSource

/-!
Unit tests for `Ix.AuxSource` (the source side of a block's auxiliaries,
`crates/compile/src/compile/aux_source.rs` in Rust): the application
telescopes. The `computeCallSitePlans` fixtures that lived here were deleted
with the legacy call-site surgery (M6R slice 6, 2026-10-07); the split-minor
helpers are exercised end to end by O2 and O11a (`pass3`, `o11a-decline`).

Registered in `Tests/Main.lean` under `aux-gen-unit`.
-/

public section

namespace Tests.AuxGen.AuxSource

open LSpec
open Ix.AuxGen
open Ix (Name Level Expr ConstantVal ConstantInfo Environment)

/-- A one-component name. -/
def nm (s : String) : Name := Name.mkStr .mkAnon s

/-! ## Telescope utilities -/

def telescopeTests : TestSeq :=
  test "collectLeanTelescope: peels a 3-arg spine in application order"
    ((let f := Expr.mkConst (nm "f") #[]
      let a1 := Expr.mkBVar 0
      let a2 := Expr.mkBVar 1
      let a3 := Expr.mkBVar 2
      let app := Expr.mkApp (Expr.mkApp (Expr.mkApp f a1) a2) a3
      let (head, args) := collectLeanTelescope app
      head == f && args == #[a1, a2, a3] : Bool))
  ++ test "collectIxonTelescope: peels a 2-arg spine in application order"
    ((let f := Ixon.Expr.ref 7 #[]
      let a1 := Ixon.Expr.var 0
      let a2 := Ixon.Expr.var 1
      let app := Ixon.Expr.app (Ixon.Expr.app f a1) a2
      let (head, args) := collectIxonTelescope app
      head == f && args == #[a1, a2] : Bool))

def suite : List TestSeq :=
  [telescopeTests]

end Tests.AuxGen.AuxSource
