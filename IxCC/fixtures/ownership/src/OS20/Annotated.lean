import Ix.Compile.SourceContract.Elab
open scoped Ix.Modes

/-!
OS20 `unique-string` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `P18UniqueString`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def addExcl (@unique s : String) : @unique String := s.push (Char.ofNat 33)
