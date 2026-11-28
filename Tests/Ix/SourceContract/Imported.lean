module

public import Ix.Compile.SourceContract.Registry
public import Ix.Compile.SourceContract.Elab
public meta import Ix.Compile.SourceContract.Resolve
public meta import Ix.Compile.SourceContract.Registry

public section

namespace Tests.Ix.SourceContract.Imported

open scoped Ix.Modes

def identity (x : Nat) : Nat := x

def withInstance {α : Type} [Inhabited α] (x : Nat) : Nat := x

opaque opaqueIdentity (x : Nat) : Nat := x

@[no_alloc, bounded_stack] def importedAsserts (x : Nat) : Nat := x + 1

structure ImportedShared where
  @shared label : Nat
  @erased proof : True
  body : Nat

open Lean Ix.Compile in
run_cmd do
  let source ← getConstInfo ``identity
  let .ok contract := SourceContract.ofTelescope source
      #[{ binder := .name `x, mode := .once, result := some .uniqueBorrowed }]
    | throwError "failed to resolve imported identity fixture"
  let .ok env := registerSourceContract (← getEnv) contract
    | throwError "failed to register imported identity fixture"
  let .ok env := registerMeasureHint env ⟨source, .name `x, some 1⟩
    | throwError "failed to register imported measure fixture"
  setEnv env
  let source ← getConstInfo ``withInstance
  let .ok contract := SourceContract.ofTelescope source #[{ binder := .position 2, mode := .once }]
    | throwError "failed to resolve implicit/instance fixture"
  let .ok env := registerSourceContract (← getEnv) contract
    | throwError "failed to register implicit/instance fixture"
  setEnv env
  let source ← getConstInfo ``opaqueIdentity
  let .ok contract := SourceContract.ofTelescope source #[{ binder := .position 0, mode := .once }]
    | throwError "failed to resolve opaque-body fixture"
  let .ok env := registerSourceContract (← getEnv) contract
    | throwError "failed to register opaque-body fixture"
  setEnv env

end Tests.Ix.SourceContract.Imported

end
