import Aiur.Library.U64
import Aiur.Library.U32.Goldilocks

/-! Explicit Goldilocks field specialization for the 64-bit word library.
The Goldilocks prime `2^64 - 2^32 + 1` exceeds `2^56`, so natural casts below
`2^56` are injective and `U64.Compatible U32.Goldilocks.F` holds. -/
namespace Aiur.Library.U64.Goldilocks
open Aiur

abbrev modulus := U32.Goldilocks.modulus
abbrev F := U32.Goldilocks.F

theorem compatible : U64.Compatible F :=
  U64.compatible_of_charP F modulus (by decide)

def declarations : Modules.Program F := U64.specialize F compatible

def program : Modules.Program F := U64.source.toField F

end Aiur.Library.U64.Goldilocks
