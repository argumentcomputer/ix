import Compilatrix.Cfg.Rc.Markers

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc


structure Program where
  base : Cfg.Program
  actions : Src.NatMap ActionTable

end Compilatrix.Cfg.Rc
