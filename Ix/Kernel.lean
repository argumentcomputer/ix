import Lean
import Ix.Environment
import Ix.Kernel.Types
import Ix.Kernel.Datatypes
import Ix.Kernel.Level
import Ix.Kernel.TypecheckM
import Ix.Kernel.Eval
import Ix.Kernel.Equal
import Ix.Kernel.Infer
import Ix.Kernel.Convert

namespace Ix.Kernel

/-- Type-checking errors from the Rust kernel, mirroring `TcError` in Rust. -/
inductive CheckError where
  | typeExpected (expr : Ix.Expr) (inferred : Ix.Expr)
  | functionExpected (expr : Ix.Expr) (inferred : Ix.Expr)
  | typeMismatch (expected : Ix.Expr) (found : Ix.Expr) (expr : Ix.Expr)
  | defEqFailure (lhs : Ix.Expr) (rhs : Ix.Expr)
  | unknownConst (name : Ix.Name)
  | duplicateUniverse (name : Ix.Name)
  | freeBoundVariable (idx : UInt64)
  | kernelException (msg : String)
  deriving Repr

/-- FFI: Run Rust kernel type-checker over all declarations in a Lean environment. -/
@[extern "rs_check_env"]
opaque rsCheckEnvFFI : @& List (Lean.Name × Lean.ConstantInfo) → IO (Array (Ix.Name × CheckError))

/-- Check all declarations in a Lean environment using the Rust kernel.
    Returns an array of (name, error) pairs for any declarations that fail. -/
def rsCheckEnv (leanEnv : Lean.Environment) : IO (Array (Ix.Name × CheckError)) :=
  rsCheckEnvFFI leanEnv.constants.toList

/-- FFI: Type-check a single constant by dotted name string. -/
@[extern "rs_check_const"]
opaque rsCheckConstFFI : @& List (Lean.Name × Lean.ConstantInfo) → @& String → IO (Option CheckError)

/-- Check a single constant by name using the Rust kernel.
    Returns `none` on success, `some err` on failure. -/
def rsCheckConst (leanEnv : Lean.Environment) (name : String) : IO (Option CheckError) :=
  rsCheckConstFFI leanEnv.constants.toList name

end Ix.Kernel
