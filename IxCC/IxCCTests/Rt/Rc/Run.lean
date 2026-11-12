import IxCCTests.Rt.Rc.Controls
import IxCCTests.Rt.Rc.GenControls
import IxCCTests.Rt.Rc.DeepControls
import IxCCTests.Rt.Rc.Native

namespace IxCCTests.Rt.Rc

def run (args : List String) : IO Unit := do
  match args with
  | ["controls"] => Controls.tests *> GenControls.tests
  | ["deep"] => DeepControls.tests
  | ["native", logs] => Native.run logs
  | _ => throw (IO.userError "expected controls, deep, or native LOGDIR")

end IxCCTests.Rt.Rc
