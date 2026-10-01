import Ix.Compile.SourceContract.Elab

/-!
OS20 `unique-string` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `P18UniqueString`. Written for Compilatr.ix (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def addExcl (! s : String) : ! String := s.push (Char.ofNat 33)
