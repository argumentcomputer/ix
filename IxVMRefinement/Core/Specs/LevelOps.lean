import IxVMRefinement.Core.Specs.Common
import IxVMRefinement.Levels.Spec

/-! # Registry family: the level operations (the levels layer's specs)

The level functions the core calls whose specs the levels layer states and proves
(`IxVM.Refinement.Levels`, `IxVMRefinement/Levels/Spec.lean`): comparisons with exact answers
(the pure functions of `Ix.IxVM.Refinement.KernelLevels`, whose meaning for `Level.eval` is
proved there), and level constructions with exact results. They read no context, so each
registry spec is the layer's spec at every context. Their steps need no induction hypothesis
(`Levels.levelLeq_step`, …). The other level functions the core calls are in
`Specs/Levels.lean`. -/

namespace IxVM.Refinement.Core.Specs.LevelOps

open IxVM.Refinement.Levels

/-- `KernelLevels::level_leq`: `LevelLeqSpec`. -/
def level_leq : SpecFn := fun _ args h r h' calls => LevelLeqSpec args h r h' calls
/-- `KernelLevels::level_equal`: `LevelEqualSpec`. -/
def level_equal : SpecFn := fun _ args h r h' calls => LevelEqualSpec args h r h' calls
/-- `KernelLevels::level_is_not_zero`: `LevelIsNotZeroSpec`. -/
def level_is_not_zero : SpecFn := fun _ args h r h' _ => LevelIsNotZeroSpec args h r h'
/-- `KernelLevels::level_struct_eq`: `LevelStructEqSpec`. -/
def level_struct_eq : SpecFn := fun _ args h r h' _ => LevelStructEqSpec args h r h'
/-- `KernelLevels::level_max`: `LevelMaxSpec`. -/
def level_max : SpecFn := fun _ args h r h' calls => LevelMaxSpec args h r h' calls
/-- `KernelLevels::level_imax`: `LevelIMaxSpec`. -/
def level_imax : SpecFn := fun _ args h r h' calls => LevelIMaxSpec args h r h' calls
/-- `KernelLevels::level_reduce`: `LevelReduceSpec`. -/
def level_reduce : SpecFn := fun _ args h r h' calls => LevelReduceSpec args h r h' calls
/-- `KernelLevels::level_inst_params`: `LevelInstParamsSpec`. -/
def level_inst_params : SpecFn := fun _ args h r h' calls => LevelInstParamsSpec args h r h' calls
/-- `KernelLevels::level_list_inst`: `LevelListInstSpec`. -/
def level_list_inst : SpecFn := fun _ args h r h' calls => LevelListInstSpec args h r h' calls

/-- The level operations. -/
inductive Fn where
  | level_leq | level_equal | level_is_not_zero | level_struct_eq | level_max | level_imax
  | level_reduce | level_inst_params | level_list_inst
  deriving DecidableEq, Repr

def Fn.name : Fn → String
  | .level_leq => "KernelLevels::level_leq"
  | .level_equal => "KernelLevels::level_equal"
  | .level_is_not_zero => "KernelLevels::level_is_not_zero"
  | .level_struct_eq => "KernelLevels::level_struct_eq"
  | .level_max => "KernelLevels::level_max"
  | .level_imax => "KernelLevels::level_imax"
  | .level_reduce => "KernelLevels::level_reduce"
  | .level_inst_params => "KernelLevels::level_inst_params"
  | .level_list_inst => "KernelLevels::level_list_inst"

def Fn.spec : Fn → SpecFn
  | .level_leq => level_leq
  | .level_equal => level_equal
  | .level_is_not_zero => level_is_not_zero
  | .level_struct_eq => level_struct_eq
  | .level_max => level_max
  | .level_imax => level_imax
  | .level_reduce => level_reduce
  | .level_inst_params => level_inst_params
  | .level_list_inst => level_list_inst

end IxVM.Refinement.Core.Specs.LevelOps
