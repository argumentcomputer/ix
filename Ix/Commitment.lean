import Lean
import Ix.Address

namespace Ix

structure Comm (α : Type 0) where
  value : Lean.Expr
  deriving Inhabited

end Ix

--inductive CommError where
--| openTerm
--| openCommitment
--| unknownConst (n: Lean.Name)
--
--structure CommCtx where
--  env : Lean.ConstMap
--
--structure CommState where
--  comms: RBMap Address 
--
--abbrev CommM := ReaderT CommCtx <| ExceptT CommError <| StateT CommState
----abbrev IxM := ReaderT IxMEnv $ ExceptT IxError $ StateT IxMState Id
