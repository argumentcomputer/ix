import Aiur.Plonk.Msg
import Aiur.Tiling.WideIxa

/-!
# The stage's tables with array-backed map matrices

`WideStage.mapFixed` reads claims by list index, so evaluating a map table's
fixed matrix row by row is quadratic. `mapFixedArr` reads the same values
from an array; `mapFixedArr_eq` makes the replacement an equality of `Air`s,
so every check of the array-backed table is a check of the stage's table.
-/

namespace Aiur.Plonk

open Aiur.Tiling.WideStage (Air mapAir mapFixed mapLengths claimsOf mapAirs)

section Generic

variable {F : Type} [Field F]

omit [Field F] in
def mapFixedArr [Zero F] [One F] (cs : Array (List F)) (i : Nat) : Nat → F
  | 0 => if i < cs.size then 1 else 0
  | k + 1 => (cs.getD i []).getD k 0

theorem mapFixedArr_eq (cs : List (List F)) : mapFixedArr cs.toArray = mapFixed cs := by
  funext i k
  cases k <;> simp [mapFixedArr, mapFixed, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- `mapAirs` with array-backed fixed matrices. -/
def mapAirsArr (claims : List (List F)) (cap : Nat → Nat) : List (Air F) :=
  (mapLengths claims).map fun L =>
    { mapAir L (claimsOf claims L) (cap L) with fixed := mapFixedArr (claimsOf claims L).toArray }

theorem mapAirsArr_eq (claims : List (List F)) (cap : Nat → Nat) :
    mapAirsArr claims cap = mapAirs claims cap := by
  simp [mapAirsArr, mapAirs, mapFixedArr_eq, mapAir]

end Generic

end Aiur.Plonk
