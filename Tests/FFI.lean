module

public import Tests.FFI.Basic
public import Tests.FFI.Ixon
public import Tests.FFI.Lifecycle
public import Tests.FFI.Refcount

/-!
  FFI test suite aggregator.
  Imports all Tests.FFI.* modules and exports a combined suite.
-/

namespace Tests.FFI

public def suiteWith (cfg : LSpec.Prop.PropertyConfig := {}) (valgrind : Bool := false) :
    LSpec.Spec := do
  Tests.FFI.Basic.suiteWith cfg
  Tests.FFI.Ixon.suiteWith cfg
  Tests.FFI.Lifecycle.suiteWith cfg
  Tests.FFI.Refcount.suiteWith cfg valgrind

public def suite : LSpec.Spec := suiteWith {} false

end Tests.FFI
