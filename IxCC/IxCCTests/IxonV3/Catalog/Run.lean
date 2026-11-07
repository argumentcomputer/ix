import IxCCTests.IxonV3.Catalog.Wire
import IxCCTests.IxonV3.Catalog.Files

namespace IxCCTests.IxonV3.CatalogTests

def run (root : System.FilePath) : IO Nat := do
  let a ← admission root
  let b ← wire
  let c ← budgets
  let d ← files root
  IO.println s!"ixon-v3-catalog-tests-ok: {a + b + c + d} admission, wire, budget, and file assertions"
  return a + b + c + d

end IxCCTests.IxonV3.CatalogTests
