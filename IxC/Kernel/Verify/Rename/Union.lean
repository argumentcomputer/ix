module

public import IxC.Kernel.Verify.Rename.Frame
public import IxC.Kernel.Verify.Extend.Inversions

@[expose] public section

/-!
# Joining two accepted lists (S1, scaffolding)

What the union of two accepted lists needs besides the frame step
(`Rename/Frame.lean`).

- **The evidence is read at operations only.** `checkDecl` consults the
  evidence table at a definition named by a structural or well-founded `Nat`
  operation, and nowhere else (`checkDecl_ev_irrel`). A list run under one
  table runs alike under any other, as long as it installs no operation.
-/

namespace Ix.Kernel

variable {md : Mode}

/-! ## The evidence is read at operations only -/

/-- **The evidence is unused** at a declaration that installs no operation. -/
theorem checkDecl_ev_irrel (mode : CheckMode) (F : Nat) (ev ev' : Evidences md) (env : Env md)
    {d : Declaration md} (hd : d.NoOp) :
    checkDecl mode (fueledOps mode F) ev env d = checkDecl mode (fueledOps mode F) ev' env d := by
  cases d with
  | defnDecl cv value hint =>
    obtain ⟨h1, h2⟩ := hd
    simp only [checkDecl]
    cases hc : checkConstantVal (fueledOps mode F) env cv with
    | error e => rfl
    | ok cv' =>
      obtain ⟨-, -, -, -, -, -, type, -, -, -, -, -, -, -, rfl⟩ := checkConstantVal_inv hc
      simp only [Bind.bind, Except.bind]
      cases checkDefnVal (fueledOps mode F) env { cv with type := type } value hint with
      | error e => rfl
      | ok env2 => simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
  | _ => rfl

end Ix.Kernel
