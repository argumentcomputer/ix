/-
  FFI test suite aggregator.
  Imports all Tests.FFI.* modules and exports a combined suite.
-/

import Tests.FFI.Basic
import Tests.FFI.Ix
import Tests.FFI.Ixon

namespace Tests.FFI

def suite : List LSpec.TestSeq :=
  Tests.FFI.Basic.suite ++ Tests.FFI.Ix.suite ++ Tests.FFI.Ixon.suite

end Tests.FFI
