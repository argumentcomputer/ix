module

public import Ix.Compile.SourceContract.Registry
public meta import Ix.Compile.SourceContract.Resolve
public meta import Ix.Compile.SourceContract.Registry

public section

namespace Tests.Ix.SourceContract.Imported

def identity (x : Nat) : Nat := x

def withInstance {α : Type} [Inhabited α] (x : Nat) : Nat := x

opaque opaqueIdentity (x : Nat) : Nat := x

open Lean Ix.Compile in
run_cmd do
  let source ← getConstInfo ``identity
  let .ok contract := SourceContract.ofTelescope source #[{ binder := .name `x, uses := .linear, resultOwned := some .unique }]
    | throwError "failed to resolve imported identity fixture"
  let .ok env := registerSourceContract (← getEnv) contract
    | throwError "failed to register imported identity fixture"
  let .ok env := registerMeasureHint env ⟨source, .name `x, some 1⟩
    | throwError "failed to register imported measure fixture"
  setEnv env
  let source ← getConstInfo ``withInstance
  let .ok contract := SourceContract.ofTelescope source #[{ binder := .position 2, uses := .affine }]
    | throwError "failed to resolve implicit/instance fixture"
  let .ok env := registerSourceContract (← getEnv) contract
    | throwError "failed to register implicit/instance fixture"
  setEnv env
  let source ← getConstInfo ``opaqueIdentity
  let .ok contract := SourceContract.ofTelescope source #[{ binder := .position 0, uses := .linear }]
    | throwError "failed to resolve opaque-body fixture"
  let .ok env := registerSourceContract (← getEnv) contract
    | throwError "failed to register opaque-body fixture"
  setEnv env

end Tests.Ix.SourceContract.Imported

end
