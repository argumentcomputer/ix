import Lean.Elab.BuiltinEvalCommand

/- Valid source declarations with auxiliary-looking names. Adding the
inductives through the kernel leaves their optional definition names available.
These are source-body controls, including a helper with the standard type. -/
run_cmd Lean.Elab.Command.liftCoreM do
  for family in [`DifferentType, `SameType, `Unrelated] do
    let name := `Tests.Ix.Compile.Fixtures.AuxiliaryIdentity ++ family ++ `Box
    Lean.addDecl <| .inductDecl [] 0 [{
      name
      type := .sort (.succ .zero)
      ctors := [{ name := name ++ `mk, type := .const name [] }]
    }] false
    Lean.compileDecls #[name]

namespace Tests.Ix.Compile.Fixtures.AuxiliaryIdentity

def DifferentType.Box.casesOn (_ : DifferentType.Box) : Nat := 7

theorem different_type : DifferentType.Box.casesOn DifferentType.Box.mk = 7 := rfl

opaque hold.{u} {α : Sort u} (value : α) : α := value

noncomputable def SameType.Box.casesOn.{u} {motive : SameType.Box → Sort u}
    (major : SameType.Box) (minor : motive SameType.Box.mk) : motive major :=
  SameType.Box.rec (hold minor) major

noncomputable def SameType.Box.recOn.{u} {motive : SameType.Box → Sort u}
    (major : SameType.Box) (minor : motive SameType.Box.mk) : motive major :=
  SameType.Box.rec (hold minor) major

theorem same_type_cases :
    SameType.Box.casesOn (motive := fun _ => Nat) SameType.Box.mk 7 = hold 7 := rfl

theorem same_type_rec :
    SameType.Box.recOn (motive := fun _ => Nat) SameType.Box.mk 7 = hold 7 := rfl

def Unrelated.Box.casesOn : Nat := 7

theorem unrelated : Unrelated.Box.casesOn = 7 := rfl

end Tests.Ix.Compile.Fixtures.AuxiliaryIdentity
