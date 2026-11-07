import IxCC.Cfg.Rc.Bounds

set_option autoImplicit false
namespace IxCCTests.Cfg.Rc
open IxCC
open IxCC.Cfg.Rc

example : instrBound 3 8 (.bind 8 (.fir (.call 3 [.var 7, .lit (.nat 1)]))) = true := by decide
example : instrBound 3 8 (.bind 8 (.fir (.call 3 [.var 8, .lit (.nat 1)]))) = false := by decide
example : instrBound 3 8 (.bind 0 (.fir (.arg (.var 8)))) = false := by decide
example : termBound 3 8 1 (.ret (.var 8)) = false := by decide

end IxCCTests.Cfg.Rc
