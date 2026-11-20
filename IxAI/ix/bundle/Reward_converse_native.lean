import IxAICore
open IxAICore

namespace IxAIReward

theorem goal : Formula.valid (.imp (.atom 0) (.atom 1)) = true :=
  by native_decide

end IxAIReward
