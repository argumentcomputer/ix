import Ix.Kernel2.Value
import Ix.Kernel2.EquivManager
import Ix.Kernel2.TypecheckM
import Ix.Kernel2.Helpers
import Ix.Kernel2.Quote
import Ix.Kernel2.Primitive
import Ix.Kernel2.Infer
import Ix.Kernel -- for CheckError type

namespace Ix.Kernel2

/-- FFI: Run Rust Kernel2 NbE type-checker over all declarations in a Lean environment. -/
@[extern "rs_check_env2"]
opaque rsCheckEnv2FFI : @& List (Lean.Name × Lean.ConstantInfo) → IO (Array (Ix.Name × Ix.Kernel.CheckError))

/-- Check all declarations in a Lean environment using the Rust Kernel2 NbE checker.
    Returns an array of (name, error) pairs for any declarations that fail. -/
def rsCheckEnv2 (leanEnv : Lean.Environment) : IO (Array (Ix.Name × Ix.Kernel.CheckError)) :=
  rsCheckEnv2FFI leanEnv.constants.toList

/-- FFI: Type-check a single constant by dotted name string using Kernel2. -/
@[extern "rs_check_const2"]
opaque rsCheckConst2FFI : @& List (Lean.Name × Lean.ConstantInfo) → @& String → IO (Option Ix.Kernel.CheckError)

/-- Check a single constant by name using the Rust Kernel2 NbE checker.
    Returns `none` on success, `some err` on failure. -/
def rsCheckConst2 (leanEnv : Lean.Environment) (name : String) : IO (Option Ix.Kernel.CheckError) :=
  rsCheckConst2FFI leanEnv.constants.toList name

/-- FFI: Type-check a batch of constants by name using Kernel2.
    Converts the environment once, then checks each name.
    Returns an array of (name, Option error) pairs. -/
@[extern "rs_check_consts2"]
opaque rsCheckConsts2FFI : @& List (Lean.Name × Lean.ConstantInfo) → @& Array String → IO (Array (String × Option Ix.Kernel.CheckError))

/-- Check a batch of constants by name using the Rust Kernel2 NbE checker. -/
def rsCheckConsts2 (leanEnv : Lean.Environment) (names : Array String) : IO (Array (String × Option Ix.Kernel.CheckError)) :=
  rsCheckConsts2FFI leanEnv.constants.toList names

/-- FFI: Convert env to Kernel2 types without type-checking.
    Returns diagnostic strings: status, kenv_size, prims_found, quot_init, missing prims. -/
@[extern "rs_convert_env2"]
opaque rsConvertEnv2FFI : @& List (Lean.Name × Lean.ConstantInfo) → IO (Array String)

/-- Convert env to Kernel2 types using Rust. Returns diagnostic array. -/
def rsConvertEnv2 (leanEnv : Lean.Environment) : IO (Array String) :=
  rsConvertEnv2FFI leanEnv.constants.toList

end Ix.Kernel2
