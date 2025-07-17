import Ix.Unsigned

namespace Archon

inductive TowerField
  | b1 | b2 | b4 | b8 | b16 | b32 | b64 | b128
  deriving Inhabited

def TowerField.logDegree : TowerField → USize
  | .b1 => 0
  | .b2 => 1
  | .b4 => 2
  | .b8 => 3
  | .b16 => 4
  | .b32 => 5
  | .b64 => 6
  | .b128 => 7

instance : ToString TowerField where
  toString
    | .b1 => "b1"
    | .b2 => "b2"
    | .b4 => "b4"
    | .b8 => "b8"
    | .b16 => "b16"
    | .b32 => "b32"
    | .b64 => "b64"
    | .b128 => "b128"

end Archon
