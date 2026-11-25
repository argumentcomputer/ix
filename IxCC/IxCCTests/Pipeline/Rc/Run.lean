import IxCCTests.Pipeline.Rc.Levels
import IxCCTests.Pipeline.Rc.Counters
import IxCCTests.Pipeline.Rc.NegativeIO
import IxCCTests.Pipeline.Rc.Wide
import IxCCTests.Pipeline.Rc.RawWords

set_option autoImplicit false
namespace IxCCTests.Pipeline.Rc

def run (args : List String) : IO Unit := do
  match args with
  | ["levels", logs] => do Levels.run logs; Wide.run none; RawWords.run none
  | ["counters", logs] => Counters.run logs
  | ["native", logs] => do
    Levels.native logs; Wide.run (some (System.FilePath.mk logs / "wide"))
    RawWords.run (some (System.FilePath.mk logs / "raw"))
  | ["negative", logs] => NegativeIO.run logs
  | ["negative", logs, reader] => NegativeIO.run logs reader
  | _ => throw (IO.userError "expected levels|counters|native|negative LOGDIR [READER]")

end IxCCTests.Pipeline.Rc
