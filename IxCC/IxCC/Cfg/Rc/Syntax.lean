import IxCC.Cfg.Rc.Markers

set_option autoImplicit false
namespace IxCC.Cfg.Rc


structure Program where
  base : Cfg.Program
  actions : Src.NatMap ActionTable

end IxCC.Cfg.Rc
