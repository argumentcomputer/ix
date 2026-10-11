import Lean.Elab.BuiltinEvalCommand

def Tests.Ix.Compile.Fixtures.AuxiliaryIdentity.BeforeOwner.Tree.below : Type := PUnit

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
  let treeName := `Tests.Ix.Compile.Fixtures.AuxiliaryIdentity.BeforeOwner.Tree
  let tree := Lean.mkConst treeName
  let field := Lean.mkConst (treeName ++ `below)
  Lean.addDecl <| .inductDecl [] 0 [{
    name := treeName
    type := .sort (.succ .zero)
    ctors := [
      { name := treeName ++ `leaf, type := tree },
      { name := treeName ++ `node,
        type := Lean.mkForall `field .default field (Lean.mkForall `child .default tree tree) }
    ]
  }] false
  Lean.compileDecls #[treeName]
  let first := `Tests.Ix.Compile.Fixtures.AuxiliaryIdentity.Changed.A
  let second := `Tests.Ix.Compile.Fixtures.AuxiliaryIdentity.Changed.B
  Lean.addDecl <| .inductDecl [] 0 [
    { name := first, type := .sort (.succ .zero),
      ctors := [{ name := first ++ `mk, type := .const first [] }] },
    { name := second, type := .sort (.succ .zero),
      ctors := [{ name := second ++ `mk, type := .const second [] }] }
  ] false
  Lean.compileDecls #[first, second]

namespace Tests.Ix.Compile.Fixtures.AuxiliaryIdentity

/-- The ordinary recursive Prop family exercises private generated below
blocks and their constructor/recursor metadata beside the custom controls. -/
inductive Witness : Nat → Prop where
  | zero : Witness 0
  | next : Witness n → Witness (n + 1)

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

def beforeOwner : BeforeOwner.Tree := BeforeOwner.Tree.node PUnit.unit BeforeOwner.Tree.leaf

theorem before_owner : beforeOwner = BeforeOwner.Tree.node PUnit.unit BeforeOwner.Tree.leaf := rfl

def Changed.A.casesOn (_ : Changed.A) : Nat := 7

noncomputable def Changed.B.casesOn.{u} {motive : Changed.B → Sort u}
    (major : Changed.B) (minor : motive Changed.B.mk) : motive major :=
  @Changed.B.rec.{u} (fun _ => PUnit.{u}) motive PUnit.unit (hold minor) major

theorem changed_type : Changed.A.casesOn Changed.A.mk = 7 := rfl

theorem changed_value : Changed.B.casesOn (motive := fun _ => Nat) Changed.B.mk 7 = hold 7 := rfl

end Tests.Ix.Compile.Fixtures.AuxiliaryIdentity
