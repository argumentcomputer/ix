import IxCC.Cfg.Rc.Public

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Public


theorem dropWrapper_block (callee : Nat) :
    (dropWrapper callee).blocks[0]? = (Native.decrementWrapper callee).blocks[0]? := rfl

theorem reps_drop (l : Lowered) : l.reps l.drop = some [.word] := by
  simp [Lowered.reps]

end IxCC.Cfg.Rc.Public
