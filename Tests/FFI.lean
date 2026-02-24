/-
  FFI test suite aggregator.
  Imports all Tests.FFI.* modules and exports a combined suite.
-/
module

public import Tests.FFI.Basic
public import Tests.FFI.Ix
public import Tests.FFI.Ixon

namespace Tests.FFI

public def suite : List LSpec.TestSeq :=
  Tests.FFI.Basic.suite ++ Tests.FFI.Ix.suite ++ Tests.FFI.Ixon.suite

end Tests.FFI
