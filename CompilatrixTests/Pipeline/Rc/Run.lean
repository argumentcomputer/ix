import CompilatrixTests.Pipeline.Rc.Levels
import CompilatrixTests.Pipeline.Rc.Counters
import CompilatrixTests.Pipeline.Rc.NegativeIO

set_option autoImplicit false
namespace CompilatrixTests.Pipeline.Rc

def run (args : List String) : IO Unit := do
  match args with
  | ["levels", logs] => Levels.run logs
  | ["counters", logs] => Counters.run logs
  | ["native", logs] => Levels.native logs
  | ["negative", logs] => NegativeIO.run logs
  | ["negative", logs, reader] => NegativeIO.run logs reader
  | _ => throw (IO.userError "expected levels|counters|native|negative LOGDIR [READER]")

end CompilatrixTests.Pipeline.Rc
