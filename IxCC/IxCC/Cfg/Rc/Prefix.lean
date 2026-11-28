import IxCC.Cfg.Rc.Markers

set_option autoImplicit false
namespace IxCC.Cfg.Rc


def encodePrefix (limit first : Nat) : List Action → List Instr
  | [] => []
  | a :: rest => marker limit first a :: encodePrefix limit (first + 1) rest

def prefixTable (first : Nat) : List Action → ActionTable
  | [] => .leaf
  | a :: rest => (prefixTable (first + 1) rest).insert first a

end IxCC.Cfg.Rc
