import IxCC.Cfg.Rc.Check
import IxCC.Own.Plain.Program

namespace IxCCTests.Cfg.Rc.Program
open IxCC IxCC.Cfg.Rc
open IxCC.Cfg (Instr)

private def source : Fir.Program :=
  { funs := Src.NatMap.ofDense [
      { key := .const 930 [], params := [(0, .tobj)],
        body := .bind 1 (.call 1 [.var 0]) (.ret (.var 1)), vars := 2 },
      { key := .const 931 [], params := [(0, .tobj)], vars := 1, body := .ret (.var 0) }]
    size := 2, exports := [0], ctors := [], known := {} }

private def bodies := (Own.Plain.Program.canonical source).bodies
private def candidate : Program :=
  (generate source bodies).getD { base := default, actions := .leaf }

private def wrongOperand : Program :=
  let fd := candidate.base.funs.getD 0 default
  let altered := { fd with blocks := fd.blocks.modifyHead fun b =>
    { b with body := .bind 2 (.fir (.call 2 [.var 1, .lit (.nat 1)])) :: b.body.drop 1 } }
  { candidate with base := { candidate.base with funs := candidate.base.funs.insert 0 altered } }

example : checkProgram source bodies candidate = true := by decide
example : checkProgram source bodies { candidate with actions := .leaf } = false := by decide
example : checkProgram source bodies
    { candidate with base := { candidate.base with funs := .leaf } } = false := by decide
example : checkProgram source bodies
    { candidate with actions := candidate.actions.insert 2 .leaf } = false := by decide
example : checkProgram source bodies
    { candidate with base := { candidate.base with funs := candidate.base.funs.insert 2 default } } = false := by decide
example : checkProgram source bodies
    { candidate with base := { candidate.base with funs := candidate.base.funs.insert 1 default } } = false := by decide
example : checkProgram source (bodies.insert 1 .trap) candidate = false := by decide
example : checkProgram source bodies
    { candidate with base := { candidate.base with size := 3 } } = false := by decide
example : checkProgram source bodies
    { candidate with base := { candidate.base with exports := [1] } } = false := by decide
example : checkProgram source bodies wrongOperand = false := by decide
example : checkProgram source bodies
    { wrongOperand with
      actions := wrongOperand.actions.insert 0
        ((wrongOperand.actions.getD 0 .leaf).insert 2 (.inc 1 1)) } = false := by decide

end IxCCTests.Cfg.Rc.Program
