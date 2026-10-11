import Lean.Elab.BuiltinEvalCommand
import Lean.Meta.Constructions.BRecOn
import Lean.Meta.Constructions.CasesOn

set_option Elab.async false

namespace Tests.Ix.Compile.Fixtures.AuxiliaryFamilyIdentity

opaque hold.{u} {α : Sort u} (value : α) : α := value

/- Each source declaration is installed through Lean's kernel. Reuse the
standard generator's exact type/universe telescope, changing only one body.
The Go case leaves brecOn's own body standard, testing transitive recognition. -/
open Lean Meta in
run_cmd Lean.Elab.Command.liftTermElabM do
  let wrap (original : DefinitionVal) (alias : Name) : MetaM Unit := do
    addDecl (.defnDecl { original with name := alias, all := [alias] })
    let value ← forallTelescope original.type fun args resultType => do
      let .sort level ← whnf (← inferType resultType) | throwError "result is not a type"
      let application := mkAppN (mkConst alias (original.levelParams.map Level.param)) args
      mkLambdaFVars args (mkApp2 (mkConst ``hold [level]) resultType application)
    addDecl (.defnDecl { original with value })
  for mode in [`Main, `Go, `Below] do
    let ns := `Tests.Ix.Compile.Fixtures.AuxiliaryFamilyIdentity ++ mode
    let even := ns ++ `Even
    let odd := ns ++ `Odd
    let type := Expr.sort (.succ .zero)
    let field (name : Name) (result : Name) :=
      mkForall `child .default (mkConst name) (mkConst result)
    addDecl <| .inductDecl [] 0 [
      { name := even, type, ctors := [
        { name := even ++ `zero, type := mkConst even },
        { name := even ++ `s, type := field odd even }] },
      { name := odd, type, ctors := [
        { name := odd ++ `s, type := field even odd }] }
    ] false
    for member in [even, odd] do mkCasesOn member
    mkBelow even
    let beforeBelow ← getEnv
    mkBelow odd
    if mode == `Below then
      let .defnInfo original ← getConstInfo (odd ++ `below) | throwError "below missing"
      setEnv beforeBelow
      wrap original (odd ++ `standardBelow)
    else
      mkBRecOn even
      let beforeBRecOn ← getEnv
      mkBRecOn odd
      let .defnInfo go ← getConstInfo (odd ++ `brecOn.go) | throwError "go missing"
      let .defnInfo original ← getConstInfo (odd ++ `brecOn) | throwError "brecOn missing"
      setEnv beforeBRecOn
      if mode == `Go then
        wrap go (odd ++ `standardGo)
        addDecl (.defnDecl original)
      else
        addDecl (.defnDecl go)
        wrap original (odd ++ `standardBRecOn)

noncomputable def Main.actual : Nat :=
  @Main.Odd.brecOn (fun _ => Nat) (fun _ => Nat) (Main.Odd.s Main.Even.zero)
    (fun _ _ => 7) (fun _ _ => 9)

theorem Main.actual_eq : Main.actual = hold 9 := rfl

noncomputable def Main.standard : Nat :=
  @Main.Even.brecOn (fun _ => Nat) (fun _ => Nat) Main.Even.zero
    (fun _ _ => 7) (fun _ _ => 9)

theorem Main.standard_eq : Main.standard = 7 := rfl

noncomputable def Go.actual : Nat :=
  @Go.Odd.brecOn (fun _ => Nat) (fun _ => Nat) (Go.Odd.s Go.Even.zero)
    (fun _ _ => 7) (fun _ _ => 9)

theorem Go.actual_eq : Go.actual =
    (hold (@Go.Odd.standardGo (fun _ => Nat) (fun _ => Nat) (Go.Odd.s Go.Even.zero)
      (fun _ _ => 7) (fun _ _ => 9))).1 := rfl

noncomputable def Below.actual : Type :=
  @Below.Odd.below (fun _ => Nat) (fun _ => Nat) (Below.Odd.s Below.Even.zero)

theorem Below.actual_eq : Below.actual =
    hold (@Below.Odd.standardBelow (fun _ => Nat) (fun _ => Nat) (Below.Odd.s Below.Even.zero)) := rfl

end Tests.Ix.Compile.Fixtures.AuxiliaryFamilyIdentity
