import CompilatrixTests.Rt.Rc.Controls
import CompilatrixTests.Rt.Rc.DeepControls
import CompilatrixTests.Rt.Rc.Native

namespace CompilatrixTests.Rt.Rc

def run (args : List String) : IO Unit := do
  match args with
  | ["controls"] => Controls.tests
  | ["deep"] => DeepControls.tests
  | ["native", logs] => Native.run logs
  | _ => throw (IO.userError "expected controls, deep, or native LOGDIR")

end CompilatrixTests.Rt.Rc
