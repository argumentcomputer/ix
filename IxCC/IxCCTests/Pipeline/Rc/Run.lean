import IxCCTests.Pipeline.Rc.Levels
import IxCCTests.Pipeline.Rc.Counters
import IxCCTests.Pipeline.Rc.NegativeIO

set_option autoImplicit false
namespace IxCCTests.Pipeline.Rc

def run (args : List String) : IO Unit := do
  match args with
  | ["levels", logs] => Levels.run logs
  | ["counters", logs] => Counters.run logs
  | ["native", logs] => Levels.native logs
  | ["negative", logs] => NegativeIO.run logs
  | ["negative", logs, reader] => NegativeIO.run logs reader
  | _ => throw (IO.userError "expected levels|counters|native|negative LOGDIR [READER]")

end IxCCTests.Pipeline.Rc
