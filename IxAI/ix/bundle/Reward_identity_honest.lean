import IxAICore
open IxAICore

namespace IxAIReward

theorem goal : Formula.valid (.imp (.atom 0) (.atom 0)) = true :=
  by decide

end IxAIReward
